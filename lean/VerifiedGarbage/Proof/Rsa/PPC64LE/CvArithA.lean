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
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcMath
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
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
open VG.Impl.Rsa.PPC64LE.CrtValues (sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr shape)
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

/-- `shape`: `r0 = 0` exactly for `Shape`, from `p_len` and `q_len` (`r20`,
`r22`) and `w`. -/
theorem shape_ok {s : State} {w pL qL : Nat} (hw : s.gpr .r29 = BitVec.ofNat 64 w)
    (hp : s.gpr .r20 = BitVec.ofNat 64 pL) (hq : s.gpr .r22 = BitVec.ofNat 64 qL) (hw' : w < 2 ^ 32)
    (hp' : pL < 2 ^ 32) (hq' : qL < 2 ^ 32) :
    WP isa (.block shape) s fun t => (t.gpr .r0 = 0 ↔ KeyCheck.Shape w pL qL) ∧ t.mem = s.mem ∧
      Keep [.r0, .r3, .r12] s t := by
  refine WP.mono (WP.keep [.r0, .r3, .r12] (Q := fun t => (t.gpr .r0 = 0 ↔ KeyCheck.Shape w pL qL) ∧
      t.mem = s.mem) (by
    unfold shape
    prun [hw, hp, hq]
    exact KeyCheck.shape_bits hw' hp' hq') (by decide)) fun t ⟨⟨h0, hm⟩, k'⟩ => ⟨h0, hm, k'⟩

/-- The first part of `arith`. -/
def partA : List (Prog isa) :=
  [.block (bitOf sPodd aP), .block shape,
    .ite (.zero .d .r0) (VG.Impl.Rsa.PPC64LE.MontKey.mulHalf aDR aP aQ .r20)
      (VG.Impl.Rsa.PPC64LE.MontKey.mulLo aDR aP aQ .r20),
    eqS sE1 aDR aDQ, .block shape,
    .ite (.zero .d .r0) (copy aDT aZero) (seqs [copy aDD aP,
      .block (VG.Impl.Rsa.PPC64LE.Keys.orOne aDD ++ VG.Impl.Rsa.PPC64LE.Keys.setOne aDR3),
      VG.Impl.Rsa.PPC64LE.MontKey.montMul aDT aDQ aDR3 aDD aDR2 .r20 VG.Impl.Rsa.PPC64LE.MontKey.cntW]),
    eqS sE2 aDT aZero]

/-- The arrays and slots `partA` writes. -/
abbrev partAArrs : List Nat := [aDR, aDD, aDT, aDR3, aDR2]
abbrev partASlots : List Nat := [sPodd, sE1, sE2]

/-- The registers `partA` changes. -/
abbrev partARegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem partA_ok {s : State} {B : Addr} {Z w Nv P Q Dd pL qL : Nat} (h : Ws s B Z w nArr)
    (hi : ArInit s.mem B w Nv P Q Dd) (h20 : s.gpr .r20 = BitVec.ofNat 64 pL)
    (h22 : s.gpr .r22 = BitVec.ofNat 64 qL) (hpL : 1 ≤ pL) (hpw : pL ≤ 4 * w) (hqw : qL ≤ 4 * w)
    (hP : P < 2 ^ (8 * pL)) (hQ : Q < 2 ^ (8 * qL)) :
    WP isa (seqs partA) s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w partAArrs partASlots s.mem t.mem ∧
      slot t.mem B sPodd = P % 2 ∧
      slot t.mem B sE1 = (if P * Q % 2 ^ (32 * w) = Nv then 1 else 0) ∧
      slot t.mem B sE2 ≤ 1 ∧
      (P % 2 = 1 → 2 ≤ P → P * Q % 2 ^ (32 * w) = Nv → (slot t.mem B sE2 = 1 ↔ Nv % P = 0)) ∧
      w32 t.mem B (arr w aDD + 4 * w) = 0 ∧ Keep partARegs s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  have hwl := h.wle
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hk : ∀ {m m' : Mem} {js ds : List Nat}, KeyWorkspace.Keep B w js ds m m' → ∀ {j : Nat}, j < nArr →
      j ∉ js → (∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) → num m' B w j = num m B w j :=
    fun k _ hj hn hd => k.num (fun x hx e => hn (by subst e; exact hx)) hd (fit _ hj)
  unfold partA
  -- `p`'s low bit.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  rw [← List.append_nil (bitOf sPodd aP)]
  refine bitOf_ok h (by decide) (by decide) (by decide) fun t1 h1 k1 o1 r1 => WP.block_nil ?_
  have p1 : num t1.mem B w aP = P := by rw [hk k1 (by decide) (by simp) (by simp; decide), hi.p]
  have q1 : num t1.mem B w aQ = Q := by rw [hk k1 (by decide) (by simp) (by simp; decide), hi.q]
  have l1 : t1.gpr .r20 = BitVec.ofNat 64 pL := (r1.gpr _ (by decide)).trans h20
  have l1' : t1.gpr .r22 = BitVec.ofNat 64 qL := (r1.gpr _ (by decide)).trans h22
  -- The guard.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shape_ok h1.r29 l1 l1' (by omega) (by omega) (by omega)) fun s1 ⟨z1, m1, ks1⟩ => ?_
  have h1s := h1.of_keep ks1
  have p1s : num s1.mem B w aP = P := by rw [m1, p1]
  have q1s : num s1.mem B w aQ = Q := by rw [m1, q1]
  have l1s : s1.gpr .r20 = BitVec.ofNat 64 pL := (ks1.gpr _ (by decide)).trans l1
  -- `p q mod 2^(32 w)`: for a balanced key over the primes' `w / 2` digits, exact.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hprod : WP isa (.ite (.zero .d .r0) (VG.Impl.Rsa.PPC64LE.MontKey.mulHalf aDR aP aQ .r20)
      (VG.Impl.Rsa.PPC64LE.MontKey.mulLo aDR aP aQ .r20)) s1 fun t2 => Ws t2 B Z w nArr ∧
        KeyWorkspace.Keep B w [aDR] [] s1.mem t2.mem ∧ num t2.mem B w aDR = P * Q % 2 ^ (32 * w) ∧
        Keep VG.Proof.Rsa.PPC64LE.MontKey.mkRegs s1 t2 := by
    refine WP.ite (s1.gpr .r0 == 0) (eval_zero s1 .r0) (fun hz => ?_) (fun _ => ?_)
    · obtain ⟨p8, hpw2, hpq, p32⟩ := z1.mp (by simpa using hz)
      refine WP.mono (VG.Proof.Rsa.PPC64LE.MontKey.mulHalf_ok h1s (by decide) (o := aDR) (x := aP) (y := aQ)
        (by decide) (by decide) (by decide) (by decide) (by decide) l1s hpL (by omega) (by decide) (by decide))
        fun t2 ⟨h2, k2, v2, r2⟩ => ⟨h2, k2, ?_, r2⟩
      have lt : ∀ {X : Nat}, X < 2 ^ (8 * pL) → X < 2 ^ (32 * ((pL + 3) / 4)) := fun hX =>
        Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) (by omega))
      have vP : val32 s1.mem B (arr w aP) ((pL + 3) / 4) = P :=
        VG.Proof.Rsa.PPC64LE.MontKey.val32_low (n := w) p1s (by omega) (lt hP)
      have vQ : val32 s1.mem B (arr w aQ) ((pL + 3) / 4) = Q :=
        VG.Proof.Rsa.PPC64LE.MontKey.val32_low (n := w) q1s (by omega) (lt (by rw [show 8 * pL = 8 * qL by omega]; exact hQ))
      have hlt : P * Q < 2 ^ (32 * w) :=
        calc P * Q < 2 ^ (32 * ((pL + 3) / 4)) * 2 ^ (32 * ((pL + 3) / 4)) :=
              Nat.mul_lt_mul'' (lt hP) (lt (by rw [show 8 * pL = 8 * qL by omega]; exact hQ))
          _ ≤ 2 ^ (32 * w) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
      rw [v2, vP, vQ, Nat.mod_eq_of_lt hlt]
    · refine WP.mono (VG.Proof.Rsa.PPC64LE.MontKey.mulLo_ok h1s (by decide) (o := aDR) (x := aP) (y := aQ)
        (by decide) (by decide) (by decide) (by decide) (by decide) l1s hpL hpw (by decide) (by decide))
        fun t2 ⟨h2, k2, v2, r2⟩ => ⟨h2, k2, ?_, r2⟩
      have vP : val32 s1.mem B (arr w aP) ((pL + 3) / 4) = P :=
        VG.Proof.Rsa.PPC64LE.MontKey.val32_low (n := w) p1s (by omega)
          (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [v2, vP, q1s]
  refine WP.mono hprod fun t2 ⟨h2, k2, v2, r2⟩ => ?_
  rw [m1] at k2
  -- `p q ≡ n`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h2 (by decide) (by decide) (by decide) (by decide)) fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  have n2 : num t2.mem B w aDQ = Nv := by
    rw [hk k2 (by decide) (by decide) (by simp), hk k1 (by decide) (by simp) (by simp; decide), hi.n]
  rw [v2, n2] at e3
  have p3 : num t3.mem B w aP = P := by
    rw [hk k3 (by decide) (by simp) (by simp; decide), hk k2 (by decide) (by decide) (by simp), p1]
  have z3 : ∀ j < 25, j ≠ aDQ → j ≠ aP → j ≠ aQ → j ≠ aD → j ∉ partAArrs → num t3.mem B w j = 0 := by
    intro j hj a b c d e
    simp only [partAArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at e
    rw [hk k3 (show j < nArr by unfold nArr; omega) (by simp) (by simp; decide),
      hk k2 (show j < nArr by unfold nArr; omega) (by simp; exact e.1) (by simp),
      hk k1 (show j < nArr by unfold nArr; omega) (by simp) (by simp; decide), hi.zero j hj a b c d]
  have n3 : num t3.mem B w aDQ = Nv := by rw [hk k3 (by decide) (by simp) (by simp; decide), n2]
  have l3 : t3.gpr .r20 = BitVec.ofNat 64 pL := (r3.gpr _ (by decide)).trans ((r2.gpr _ (by decide)).trans l1s)
  have l3' : t3.gpr .r22 = BitVec.ofNat 64 qL :=
    (r3.gpr _ (by decide)).trans ((r2.gpr _ (by decide)).trans ((ks1.gpr _ (by decide)).trans l1'))
  have top3 : w32 t3.mem B (arr w aDD + 4 * w) = 0 := by
    rw [KeyWorkspace.Keep.word k3 (i := w) (by omega) (by simp) (by simp; decide) (fit _ (by decide)),
      KeyWorkspace.Keep.word k2 (i := w) (by omega) (by decide) (by simp) (fit _ (by decide)),
      KeyWorkspace.Keep.word k1 (i := w) (by omega) (by simp) (by simp; decide) (fit _ (by decide)),
      hi.top _ (by decide)]
  -- The guard again.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shape_ok h3.r29 l3 l3' (by omega) (by omega) (by omega)) fun s7 ⟨z7, m7, ks7⟩ => ?_
  have h7s := h3.of_keep ks7
  -- `0` for a balanced key, else Montgomery's `n` modulo `p | 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hmn : WP isa (.ite (.zero .d .r0) (copy aDT aZero) (seqs [copy aDD aP,
      .block (VG.Impl.Rsa.PPC64LE.Keys.orOne aDD ++ VG.Impl.Rsa.PPC64LE.Keys.setOne aDR3),
      VG.Impl.Rsa.PPC64LE.MontKey.montMul aDT aDQ aDR3 aDD aDR2 .r20 VG.Impl.Rsa.PPC64LE.MontKey.cntW])) s7
      fun t7 => Ws t7 B Z w nArr ∧ KeyWorkspace.Keep B w [aDT, aDR2, aDD, aDR3] [] s7.mem t7.mem ∧
        w32 t7.mem B (arr w aDD + 4 * w) = 0 ∧
        (P % 2 = 1 → 2 ≤ P → P * Q % 2 ^ (32 * w) = Nv → (num t7.mem B w aDT = 0 ↔ Nv % P = 0)) ∧
        Keep partARegs s7 t7 := by
    refine WP.ite (s7.gpr .r0 == 0) (eval_zero s7 .r0) (fun hz => ?_) (fun _ => ?_)
    · obtain ⟨p8, hpw2, hpq, p32⟩ := z7.mp (by simpa using hz)
      refine WP.mono (copy_ok h7s (o := aDT) (a := aZero) (by decide) (by decide) (by decide) (by decide))
        fun t7 ⟨h7, k7, v7, r7, _⟩ => ⟨h7, k7.mono, ?_, fun podd p2 hL => ?_, r7.mono⟩
      · rw [KeyWorkspace.Keep.word k7 (i := w) (by omega) (by decide) (by simp) (fit _ (by decide)), m7, top3]
      · have hlt : P * Q < 2 ^ (32 * w) :=
          calc P * Q < 2 ^ (8 * pL) * 2 ^ (8 * qL) := Nat.mul_lt_mul'' hP hQ
            _ = 2 ^ (32 * w) := by rw [← Nat.pow_add]; congr 1; omega
        rw [Nat.mod_eq_of_lt hlt] at hL
        rw [v7, m7, z3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ← hL,
          Nat.mul_mod_right]
    · rw [wp_seqs_cons (List.cons_ne_nil _ _)]
      refine WP.mono (copy_ok h7s (o := aDD) (a := aP) (by decide) (by decide) (by decide) (by decide))
        fun t4 ⟨h4, k4, v4, r4, _⟩ => ?_
      rw [wp_seqs_cons (List.cons_ne_nil _ _)]
      refine orOne_ok h4 (j := aDD) (by decide) (by decide) fun t5 h5 k5 v5 r5 => ?_
      rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.setOne aDR3)]
      refine setOne_ok h5 (j := aDR3) (by decide) (by decide) fun t6 h6 k6 v6 r6 => WP.block_nil ?_
      have m6 : num t6.mem B w aDD = 2 * (P / 2) + 1 := by
        rw [hk k6 (by decide) (by decide) (by simp), v5, v4, m7, p3]
      have o6 : num t6.mem B w aDR3 = 1 := by
        rw [v6, hk k5 (by decide) (by decide) (by simp), hk k4 (by decide) (by decide) (by simp), m7,
          hk k3 (by decide) (by simp) (by simp; decide), hk k2 (by decide) (by decide) (by simp),
          hk k1 (by decide) (by simp) (by simp; decide), hi.zero _ (by decide) (by decide) (by decide) (by decide)
            (by decide)]
      have n6 : num t6.mem B w aDQ = Nv := by
        rw [hk k6 (by decide) (by decide) (by simp), hk k5 (by decide) (by decide) (by simp),
          hk k4 (by decide) (by decide) (by simp), m7, n3]
      have l6 : t6.gpr .r20 = BitVec.ofNat 64 pL := by
        rw [r6.gpr _ (by decide), r5.gpr _ (by decide), r4.gpr _ (by decide), ks7.gpr _ (by decide)]; exact l3
      have pw' : 2 ^ (8 * pL) ≤ 2 ^ (32 * ((pL + 3) / 4)) := Nat.pow_le_pow_right (by decide) (by omega)
      have hm : 2 * (P / 2) + 1 < 2 ^ (8 * pL) := by
        have : 2 ^ (8 * pL) = 2 * 2 ^ (8 * pL - 1) := by rw [← Nat.pow_succ']; congr 1; omega
        omega
      refine WP.mono (VG.Proof.Rsa.PPC64LE.MontKey.montMul_ok h6 (by decide) (a := aDT) (x := aDQ) (y := aDR3)
        (m := aDD) (tt := aDR2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l6 hpL (by omega) (by decide)
        (by decide) m6 (Nat.lt_of_lt_of_le hm pw') (by omega) o6 (Nat.one_lt_two_pow (by omega)))
        fun t7 ⟨h7, k7, _, _, top7, cg7, r7⟩ => ⟨h7, (k4.mono.trans (k5.mono.trans (k6.mono.trans k7.mono))), top7,
          fun podd p2 _ => ?_, (((r4.trans r5).trans r6).trans r7).mono⟩
      have e1 : 2 * (P / 2) + 1 = P := by omega
      rw [e1] at cg7
      obtain ⟨lt, cg⟩ := cg7 (by omega)
      rw [Nat.mul_one, n6] at cg
      exact VG.Proof.Rsa.mont_zero_iff podd lt cg
  refine WP.mono hmn fun t7 ⟨h7, k7, top7, mc7, r7⟩ => ?_
  rw [m7] at k7
  -- `M = 0`.
  refine WP.mono (eqS_ok h7 (by decide) (by decide) (by decide) (by decide)) fun t ⟨h8, k8, e8, r8⟩ => ?_
  have z7 : num t7.mem B w aZero = 0 := by
    rw [hk k7 (by decide) (by decide) (by simp)]
    exact z3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [z7] at e8
  refine ⟨h8, ?_, ?_, ?_, ?_, fun podd p2 hL => ?_, ?_, ?_⟩
  · exact k1.mono.trans (k2.mono.trans (k3.mono.trans (k7.mono.trans k8.mono)))
  · rw [k8.slot (by decide) (by decide), k7.slot (by decide) (by simp), k3.slot (by decide) (by decide),
      k2.slot (by decide) (by simp), o1, hi.p]
  · rw [k8.slot (by decide) (by decide), k7.slot (by decide) (by simp), e3]
  · rw [e8]; split <;> omega
  · rw [e8, ← mc7 podd p2 hL]
    split <;> simp_all
  · rw [KeyWorkspace.Keep.word k8 (i := w) (by omega) (by simp) (by simp; decide) (fit _ (by decide)), top7]
  · exact ((((r1.trans ks1).trans r2).trans r3).trans ((ks7.trans r7).trans r8)).mono

end VG.Proof.Rsa.PPC64LE.CrtValues
