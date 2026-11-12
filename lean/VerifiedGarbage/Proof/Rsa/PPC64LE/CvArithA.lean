module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Proof.Rsa.PPC64LE.DivLoop
import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.PPC64LE.DivN
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Div
public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyArrays
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
import VerifiedGarbage.Proof.Rsa.PPC64LE.MontKey
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Rsa.MontCheckMath

/-!
# `vg_rsa_crt_values` on PPC64LE: the arithmetic, `p q = n`

The arrays at the start of `arith` (`ArInit`): `n`, `p`, `q` and `d` in
`aDQ`, `aP`, `aQ` and `aD`, every other array 0, and every array's extra
digit 0. `partA_ok`: `p`'s low bit, whether `p q ≡ n (mod 2^(32 w))`, and
whether Montgomery's `n` modulo `p | 1` is 0, which for an odd `p ≥ 2` is
whether `p ∣ n`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy bitOf eqS aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.Div (div divP)
open VG.Impl.Rsa.PPC64LE.CrtValues (sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The arrays at the start of `arith`. -/
structure ArInit (m : Mem) (B : Addr) (w Nv P Q Dd : Nat) : Prop where
  n : num m B w aDQ = Nv
  p : num m B w aP = P
  q : num m B w aQ = Q
  d : num m B w aD = Dd
  zero : ∀ j < 25, j ≠ aDQ → j ≠ aP → j ≠ aQ → j ≠ aD → num m B w j = 0
  top : ∀ j < 25, w32 m B (arr w j + 4 * w) = 0

/-- A number of `w + 1` digits below `2^(32 w)` is its low `w` digits. -/
theorem num_of_num1 {m : Mem} {B : Addr} {w j : Nat} (h : num1 m B w j < 2 ^ (32 * w)) :
    num m B w j = num1 m B w j := by
  have e := val32_append m B (arr w j) w 1
  have hl := val32_lt m B (arr w j) w
  change val32 _ _ _ (w + 1) < _ at h
  change val32 _ _ _ w = val32 _ _ _ (w + 1)
  rw [e] at h ⊢
  have : val32 m B (arr w j + 4 * w) 1 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (arr w j + 4 * w) 1) with z | z
    · exact z
    · have : 2 ^ (32 * w) ≤ 2 ^ (32 * w) * val32 m B (arr w j + 4 * w) 1 := Nat.le_mul_of_pos_right _ z
      omega_arith
  rw [this, Nat.mul_zero, Nat.add_zero]

/-- The first part of `arith`. -/
def partA : List (Prog isa) :=
  [.block (bitOf sPodd aP), VG.Impl.Rsa.PPC64LE.MontKey.mulLo aDR aP aQ .r20, eqS sE1 aDR aDQ, copy aDD aP,
    .block (VG.Impl.Rsa.PPC64LE.Keys.orOne aDD ++ VG.Impl.Rsa.PPC64LE.Keys.setOne aDR3),
    VG.Impl.Rsa.PPC64LE.MontKey.montMul aDT aDQ aDR3 aDD aDR2 .r20 VG.Impl.Rsa.PPC64LE.MontKey.cntW,
    eqS sE2 aDT aZero]

/-- The arrays and slots `partA` writes. -/
abbrev partAArrs : List Nat := [aDR, aDD, aDT, aDR3, aDR2]
abbrev partASlots : List Nat := [sPodd, sE1, sE2]

/-- The registers `partA` changes. -/
abbrev partARegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem partA_ok {s : State} {B : Addr} {Z w Nv P Q Dd pL : Nat} (h : Ws s B Z w nArr)
    (hi : ArInit s.mem B w Nv P Q Dd) (h20 : s.gpr .r20 = BitVec.ofNat 64 pL) (hpL : 1 ≤ pL)
    (hpw : pL ≤ 4 * w) (hP : P < 2 ^ (8 * pL)) :
    WP isa (seqs partA) s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w partAArrs partASlots s.mem t.mem ∧
      slot t.mem B sPodd = P % 2 ∧
      slot t.mem B sE1 = (if P * Q % 2 ^ (32 * w) = Nv then 1 else 0) ∧
      slot t.mem B sE2 ≤ 1 ∧ (P % 2 = 1 → 2 ≤ P → (slot t.mem B sE2 = 1 ↔ Nv % P = 0)) ∧
      w32 t.mem B (arr w aDD + 4 * w) = 0 ∧ Keep partARegs s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hk : ∀ {m m' : Mem} {js ds : List Nat}, KeyWorkspace.Keep B w js ds m m' → ∀ {j : Nat}, j < nArr →
      j ∉ js → (∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) → num m' B w j = num m B w j :=
    fun k _ hj hn hd => k.num (fun x hx e => hn (by subst e; exact hx)) hd (fit _ hj)
  unfold partA
  -- `p`'s low bit.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  rw [← List.append_nil (bitOf sPodd aP)]
  refine bitOf_ok h (by decide) (by decide) (by decide) fun t1 h1 k1 o1 r1 => WP.block_nil ?_
  have p1 : num s.mem B w aP = P := hi.p
  -- `p q mod 2^(32 w)`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have l1 : t1.gpr .r20 = BitVec.ofNat 64 pL := (r1.gpr _ (by decide)).trans h20
  refine WP.mono (VG.Proof.Rsa.PPC64LE.MontKey.mulLo_ok h1 (by decide) (o := aDR) (x := aP) (y := aQ)
    (by decide) (by decide) (by decide) (by decide) (by decide) l1 hpL hpw (by decide) (by decide))
    fun t2 ⟨h2, k2, v2, r2⟩ => ?_
  have vP : val32 t1.mem B (arr w aP) ((pL + 3) / 4) = P :=
    VG.Proof.Rsa.PPC64LE.MontKey.val32_low (n := w)
      (by show num t1.mem B w aP = P; rw [hk k1 (by decide) (by simp) (by simp; decide), p1]) (by omega)
      (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) (by omega)))
  have q1 : num t1.mem B w aQ = Q := by rw [hk k1 (by decide) (by simp) (by simp; decide), hi.q]
  rw [vP, q1] at v2
  -- `p q ≡ n`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h2 (by decide) (by decide) (by decide) (by decide)) fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  have n2 : num t2.mem B w aDQ = Nv := by
    rw [hk k2 (by decide) (by decide) (by simp), hk k1 (by decide) (by simp) (by simp; decide), hi.n]
  rw [v2, n2] at e3
  -- `p | 1`, and 1 in `aDR3`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h3 (by decide) (by decide) (by decide) (by decide)) fun t4 ⟨h4, k4, v4, r4, top4⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine orOne_ok h4 (j := aDD) (by decide) (by decide) fun t5 h5 k5 v5 r5 => ?_
  rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.setOne aDR3)]
  refine setOne_ok h5 (j := aDR3) (by decide) (by decide) fun t6 h6 k6 v6 r6 => WP.block_nil ?_
  have p3 : num t3.mem B w aP = P := by
    rw [hk k3 (by decide) (by simp) (by simp; decide), hk k2 (by decide) (by decide) (by simp),
      hk k1 (by decide) (by simp) (by simp; decide), p1]
  have m6 : num t6.mem B w aDD = 2 * (P / 2) + 1 := by
    rw [hk k6 (by decide) (by decide) (by simp), v5, v4, p3]
  have o6 : num t6.mem B w aDR3 = 1 := by
    rw [v6, hk k5 (by decide) (by decide) (by simp), hk k4 (by decide) (by decide) (by simp),
      hk k3 (by decide) (by simp) (by simp; decide), hk k2 (by decide) (by decide) (by simp),
      hk k1 (by decide) (by simp) (by simp; decide), hi.zero _ (by decide) (by decide) (by decide) (by decide)
        (by decide)]
  have n6 : num t6.mem B w aDQ = Nv := by
    rw [hk k6 (by decide) (by decide) (by simp), hk k5 (by decide) (by decide) (by simp),
      hk k4 (by decide) (by decide) (by simp), hk k3 (by decide) (by simp) (by simp; decide), n2]
  -- Montgomery's `n`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have l6 : t6.gpr .r20 = BitVec.ofNat 64 pL := by
    rw [r6.gpr _ (by decide), r5.gpr _ (by decide), r4.gpr _ (by decide), r3.gpr _ (by decide),
      r2.gpr _ (by decide)]; exact l1
  have pw' : 2 ^ (8 * pL) ≤ 2 ^ (32 * ((pL + 3) / 4)) := Nat.pow_le_pow_right (by decide) (by omega)
  have hm : 2 * (P / 2) + 1 < 2 ^ (8 * pL) := by
    have : 2 ^ (8 * pL) = 2 * 2 ^ (8 * pL - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    omega
  refine WP.mono (VG.Proof.Rsa.PPC64LE.MontKey.montMul_ok h6 (by decide) (a := aDT) (x := aDQ) (y := aDR3)
    (m := aDD) (tt := aDR2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l6 hpL (by omega) (by decide)
    (by decide) m6 (Nat.lt_of_lt_of_le hm pw') (by omega) o6 (Nat.one_lt_two_pow (by omega)))
    fun t7 ⟨h7, k7, _, _, top7, cg7, r7⟩ => ?_
  -- `M = 0`.
  refine WP.mono (eqS_ok h7 (by decide) (by decide) (by decide) (by decide)) fun t ⟨h8, k8, e8, r8⟩ => ?_
  have z7 : num t7.mem B w aZero = 0 := by
    rw [hk k7 (by decide) (by decide) (by simp), hk k6 (by decide) (by decide) (by simp),
      hk k5 (by decide) (by decide) (by simp), hk k4 (by decide) (by decide) (by simp),
      hk k3 (by decide) (by simp) (by simp; decide), hk k2 (by decide) (by decide) (by simp),
      hk k1 (by decide) (by simp) (by simp; decide), hi.zero _ (by decide) (by decide) (by decide) (by decide)
        (by decide)]
  rw [z7] at e8
  refine ⟨h8, ?_, ?_, ?_, ?_, fun podd p2 => ?_, ?_, ?_⟩
  · exact k1.mono.trans (k2.mono.trans (k3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans
      (k7.mono.trans k8.mono))))))
  · rw [k8.slot (by decide) (by decide), k7.slot (by decide) (by simp), k6.slot (by decide) (by simp),
      k5.slot (by decide) (by simp), k4.slot (by decide) (by simp), k3.slot (by decide) (by decide),
      k2.slot (by decide) (by simp), o1, p1]
  · rw [k8.slot (by decide) (by decide), k7.slot (by decide) (by simp), k6.slot (by decide) (by simp),
      k5.slot (by decide) (by simp), k4.slot (by decide) (by simp), e3]
  · rw [e8]; split <;> omega
  · have e1 : 2 * (P / 2) + 1 = P := by omega
    rw [e1] at cg7
    obtain ⟨lt, cg⟩ := cg7 (by omega)
    rw [Nat.mul_one, n6] at cg
    rw [e8, ← VG.Proof.Rsa.mont_zero_iff podd lt cg]
    split <;> simp_all
  · rw [KeyWorkspace.Keep.word k8 (i := w) (by omega) (by simp) (by simp; decide) (fit _ (by decide)), top7]
  · exact ((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans (r7.trans r8)).mono

end VG.Proof.Rsa.PPC64LE.CrtValues
