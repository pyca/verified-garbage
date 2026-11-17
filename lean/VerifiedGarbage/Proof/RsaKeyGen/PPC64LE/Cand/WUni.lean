module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Witness
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Bits
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Copy
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Gcd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `RsaKeyGen.PPC64LE.Cand.Close`, which this module and modules that import it used -/

section

/-!
# A candidate on PPC64LE: too close to `p`

`sub_ok`: `[o] := [a] − [b]` by `subMod`, its borrow's mask in `r20`.
`closeCheck_ok`: `r22` is whether `c` (array 0) is too close to `p`, the
`p_len` octets at `P` (`r18`, `r19`): `|c − p| ≤ 2^(64 w − 100)`, by `c − p`,
`p − c`, the one that does not borrow, and the borrow of the bound minus it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (seqs sub loadP closeCalc closeCheck aP aD1 aD2 aAbs aBnd aTmp nArr)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.Bignum (slot wv)

/-- The registers `sub` writes. -/
def subRegs : List Reg := [.r0, .r3, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r20]

/-- `sub o a b`: `[o] := [a] − [b]`, with the borrow `c`, for `[a]` whose
digit `2 w` is zero; the mask of `c` in `r20`. -/
theorem sub_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z) {o a b : Nat}
    (ho : o < nArr) (ha : a < nArr) (hb : b < nArr) (hoa : o ≠ a) (hob : o ≠ b)
    (hz : w32 s.mem B (slot w a + 8 * w) = 0) :
    WP isa (sub o a b) s fun t =>
      (∃ c ≤ 1, val32 t.mem B (slot w o) (2 * w) + val32 s.mem B (slot w b) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) + 2 ^ (64 * w) * c ∧ t.gpr .r20 = BitVec.ofNat 64 0 - BitVec.ofNat 64 c) ∧
        Env t B Z w ∧ Outside B (slot w o) (8 * w) s.mem t.mem ∧ Keep subRegs s t := by
  have hw4 := h.hw
  have hw128 := h.hw'
  obtain hO := Nat.le_trans (VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) ho) h35
  obtain hA := Nat.le_trans (VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) ha) h35
  obtain hB := Nat.le_trans (VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) hb) h35
  obtain soa := VG.Proof.Bignum.slot_sep (w := w) hoa
  obtain sob := VG.Proof.Bignum.slot_sep (w := w) hob
  unfold sub
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .r8) (by decide) (by decide) a) fun t₁ ⟨⟨a8, m₁⟩, k₁⟩ => ?_
  obtain e₁ := h.keep k₁ (by decide)
  refine WP.mono (e₁.base (rd := .r9) (by decide) (by decide) o) fun t₂ ⟨⟨a9, m₂⟩, k₂⟩ => ?_
  obtain e₂ := e₁.keep k₂ (by decide)
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) e₂.h10 e₂.h29 b) fun t₃ ⟨⟨a10, m₃⟩, k₃⟩ => ?_
  obtain hm : t₃.mem = s.mem := by rw [m₃, m₂, m₁]
  obtain k13 := (k₁.trans k₂).trans k₃
  obtain hs₃ := h.hs.congr k13.wr
  refine WP.seq (WP.mono (subMod_ok hs₃ (dA := slot w a) (dT := slot w o) (dM := slot w b) (n := 2 * w)
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), a8]) (by rw [k₃.gpr _ (by decide), a9]) a10
    (by rw [k13.gpr _ (by decide)]; exact h.h11) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith)) fun t₄ ⟨⟨c, hc, hv, h20⟩, out₄, k₄⟩ => ?_)
  rw [hm] at hv h20 out₄
  rw [show slot w a + 4 * (2 * w) = slot w a + 8 * w by omega_arith, hz] at h20
  obtain k14 := k13.trans k₄
  refine WP.mono (WP.keep [.r10] (Q := fun u => u.gpr .r10 = off B (slot w 0) ∧ u.mem = t₄.mem) (by
    prun [(k14.gpr .r31 (by decide)).trans h.h31, VG.Impl.Bignum.hdrBytes]
    show B + BitVec.ofNat 64 256 = B + BitVec.ofNat 64 (slot w 0)
    rw [slot0]) (by decide)) fun t ⟨⟨t10, tm⟩, kt⟩ => ?_
  obtain K := k14.trans kt
  refine ⟨⟨c, hc, ?_, ?_⟩, ⟨h.hs.congr K.wr, t10, ?_, ?_, ?_, hw4, hw128, h.hZ⟩, ?_, K.mono (by simp [subRegs])⟩
  · rw [tm, show 64 * w = 32 * (2 * w) by omega_arith]; exact hv
  · rw [kt.gpr _ (by decide), h20]
    rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl <;> rfl
  · rw [K.gpr _ (by decide)]; exact h.h29
  · rw [K.gpr _ (by decide)]; exact h.h11
  · rw [K.gpr _ (by decide)]; exact h.h31
  · rw [tm, show 8 * w = 4 * (2 * w) by omega_arith]; exact out₄

/-- An array apart from the `w` words of another that changed keeps its value. -/
theorem out_val {B : Addr} {w o j : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * w) m m') (hj : j ≠ o)
    (hn : slot w nArr ≤ 2 ^ 64) (hj' : j < nArr) :
    val32 m' B (slot w j) (2 * w) = val32 m B (slot w j) (2 * w) := by
  have := VG.Proof.Bignum.slot_sep (w := w) hj
  have := VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) hj'
  have := slot_le (w := w) (show j + 1 ≤ nArr by omega_arith)
  exact h.val32 (by omega_arith) (by omega_arith)

/-- Digit `2 w` of an array, which no change of the `w` words of an array
reaches. -/
theorem out_top {B : Addr} {w o j : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * w) m m')
    (hn : slot w nArr ≤ 2 ^ 64) (ho : o < nArr) (hj : j < nArr) :
    w32 m' B (slot w j + 8 * w) = w32 m B (slot w j + 8 * w) := by
  have := VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) hj
  have := slot_le (w := w) (show j + 1 ≤ nArr by omega_arith)
  by_cases e : j = o
  · subst e; exact h.w32 (by omega_arith) (by omega_arith)
  · have := VG.Proof.Bignum.slot_sep (w := w) e
    exact h.w32 (by omega_arith) (by omega_arith)

/-- `loadP`: `p`'s `8 w` octets at `P` (`r18`) into `aP`. -/
theorem loadP_ok {s : State} {B P : Addr} {Z w : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z) (h18 : s.gpr .r18 = P)
    (h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * w)) (hP : ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off P i) 1)
    (hsep : ∀ i < 8 * w, ∀ x, ofs B x < Z → off P i ≠ x) :
    WP isa loadP s fun t =>
      (val32 t.mem B (slot w aP) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P (8 * w)) ∧
        Env t B Z w ∧ Outside B (slot w aP) (8 * w) s.mem t.mem) ∧
        Keep [.r0, .r6, .r10, .r12, .r14, .r15, .r16, .r17] s t := by
  have hw4 := h.hw
  have hw128 := h.hw'
  obtain hA := Nat.le_trans (VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) (show aP < nArr by decide)) h35
  unfold loadP
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) h.h10 h.h29 aP) fun t₁ ⟨⟨a10, m₁⟩, k₁⟩ => ?_
  obtain hpre : WP isa (.block [.addi .r12 .r18 0, .addi .r6 .r24 0]) t₁ fun u =>
      (u.gpr .r12 = off P 0 ∧ u.gpr .r6 = BitVec.ofNat 64 (8 * w) ∧ u.mem = t₁.mem) ∧ Keep [.r6, .r12] t₁ u := by
    refine WP.keep _ ?_ (by decide)
    prun [(k₁.gpr _ (by decide)).trans h18, (k₁.gpr _ (by decide)).trans h24]
    exact BitVec.add_zero _
  refine WP.mono hpre fun u ⟨⟨u12, u6, um⟩, ku⟩ => ?_
  obtain k1u := k₁.trans ku
  refine WP.seq (WP.mono (loadN_ok (h.hs.congr k1u.wr) (dA := slot w aP) ((ku.gpr _ (by decide)).trans a10) u12 u6
    (by rw [k1u.gpr _ (by decide)]; exact h.h11) (by omega_arith) (Nat.le_refl _) (by omega_arith)
    (by simp only [slot, VG.Impl.Bignum.hdrBytes]; omega_arith) (by omega_arith) (fun i hi => by rw [k1u.rd, k1u.wr]; exact hP i hi) hsep)
    fun v ⟨vv, vout, kv⟩ => ?_)
  rw [um, m₁] at vv vout
  obtain k1v := k1u.trans kv
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = v.mem) (by
    prun [(k1v.gpr .r31 (by decide)).trans h.h31, VG.Impl.Bignum.hdrBytes]
    show B + BitVec.ofNat 64 256 = B + BitVec.ofNat 64 (slot w 0)
    rw [slot0]) (by decide)) fun t ⟨⟨t10, tm⟩, kt⟩ => ?_
  obtain K := k1v.trans kt
  refine ⟨⟨by rw [tm]; exact vv, ⟨h.hs.congr K.wr, t10, ?_, ?_, ?_, hw4, hw128, h.hZ⟩, by rw [tm]; exact vout⟩,
    K.mono (by simp)⟩
  · rw [K.gpr _ (by decide)]; exact h.h29
  · rw [K.gpr _ (by decide)]; exact h.h11
  · rw [K.gpr _ (by decide)]; exact h.h31

/-- A number of words all zero but word `k`. -/
theorem wv_single {m : Mem} {p : Addr} {d k : Nat} {v : BitVec 64}
    (hk : VG.Proof.Bignum.word m p (d + 8 * k) = v) :
    ∀ n, (∀ i < n, i ≠ k → VG.Proof.Bignum.word m p (d + 8 * i) = 0) →
      wv m p d n = if k < n then v.toNat * 2 ^ (64 * k) else 0
  | 0, _ => by simp [wv]
  | n + 1, hz => by
    rw [wv, wv_single hk n fun i hi hik => hz i (by omega_arith) hik]
    by_cases e : n = k
    · subst e; rw [hk]; simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self, Nat.zero_add]
      exact Nat.mul_comm _ _
    · rw [hz n (by omega_arith) e]
      by_cases hl : k < n
      · simp only [hl, ↓reduceIte, show k < n + 1 by omega_arith]; simp
      · simp only [hl, ↓reduceIte, show ¬ k < n + 1 by omega_arith]; simp

theorem lis_eq : BitVec.signExtend 64 ((4096 : BitVec 16) ++ (0 : BitVec 16)) = (268435456#64 : BitVec 64) := by
  decide

/-- The bound `2^(64 w − 100)` into `aBnd`: word `w − 2` := `2^28`. -/
theorem bound_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z) :
    WP isa (.block (base .r5 aBnd ++ ([.lsl .r6 .r11 2, .add .r5 .r5 .r6, .subi .r5 .r5 16, .lis .r0 0x1000,
      .store .d .r0 .r5 0] : List Instr))) s fun t =>
      (t.mem = s.mem.writeW (off B (slot w aBnd + 8 * (w - 2))) (BitVec.ofNat 64 (2 ^ 28))) ∧
        Keep [.r0, .r5, .r6] s t := by
  have hw4 := h.hw
  have hw128 := h.hw'
  obtain hA := Nat.le_trans (VG.Proof.MillerRabin.PPC64LE.slot_lt (w := w) (show aBnd < nArr by decide)) h35
  have hnw := h.hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r5) (by decide) (by decide) aBnd) fun t₁ ⟨⟨a5, m₁⟩, k₁⟩ => ?_
  obtain hs₁ := h.hs.congr k₁.wr
  obtain e5 : off B (slot w aBnd) + (BitVec.ofNat 64 (2 * w) <<< 2) - BitVec.ofNat 64 16 =
      off B (slot w aBnd + 8 * (w - 2)) := by
    obtain e8 : BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_arith
    rw [e8, off_add, Offset.add_ofNat_sub _ (show 16 ≤ slot w aBnd + 8 * w by omega_arith),
      show slot w aBnd + 8 * w - 16 = slot w aBnd + 8 * (w - 2) by omega_arith]
  obtain hst := hs₁.st (d := slot w aBnd + 8 * (w - 2)) (n := 8) (by omega_arith)
  refine WP.mono (WP.keep [.r0, .r5, .r6] (Q := fun t =>
      t.mem = t₁.mem.writeW (off B (slot w aBnd + 8 * (w - 2))) (BitVec.ofNat 64 (2 ^ 28))) ?_ (by decide))
    fun t ⟨tm, kt⟩ => ⟨by rw [tm, m₁], (k₁.trans kt).mono⟩
  prun [a5, (k₁.gpr _ (by decide)).trans h.h11, exec_lis, lis_eq, e5, hst]
  done

/-- A change within one of the arrays `aP` to `aTmp`. -/
theorem into_close {B : Addr} {w j n : Nat} {m m' : Mem} (h : Outside B (slot w j) n m m') (hj : aP ≤ j)
    (hj' : j ≤ aTmp) (hn : n ≤ 8 * (w + 2)) : Outside B (slot w aP) (6 * (8 * (w + 2))) m m' := by
  simp only [aP, aTmp] at hj hj'
  refine h.mono ?_ ?_
  · rw [slot_lin, slot_lin]; have := Nat.mul_le_mul_right (8 * w) hj; simp only [aP] at this ⊢; omega_arith
  · rw [slot_lin, slot_lin]; have := Nat.mul_le_mul_right (8 * w) hj'; simp only [aP] at this ⊢; omega_arith

/-- The registers the check writes. -/
def ccRegs : List Reg := [.r0, .r3, .r5, .r6, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r20, .r22]

/-- The borrow of `x − y` for `x, y < R`, from `D + y = x + R b` with `D < R`. -/
theorem borrow_iff {x y D R b : Nat} (hb : b ≤ 1) (h : D + y = x + R * b) (hD : D < R) (hy : y < R) :
    (b = 1 ↔ x < y) ∧ (b = 0 → D = x - y) ∧ (b = 1 → D = R + x - y) := by
  rcases (show b = 0 ∨ b = 1 by omega_arith) with rfl | rfl <;> omega_arith

theorem flag_final (b : Nat) (hb : b ≤ 1) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 b) &&& BitVec.ofNat 64 1 ^^^ BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (if b = 1 then 0 else 1) := by
  rcases (show b = 0 ∨ b = 1 by omega_arith) with rfl | rfl <;> decide

/-- The check's arithmetic: `|c − p|` from the differences, and the bound's
borrow. -/
theorem close_math {c p D1 D2 A T Bd R b1 b2 b3 : Nat} (hb1 : b1 ≤ 1) (hb2 : b2 ≤ 1)
    (hb3 : b3 ≤ 1) (h1 : D1 + p = c + R * b1) (hD1 : D1 < R) (h2 : D2 + c = p + R * b2) (hD2 : D2 < R)
    (hA : A = if b1 = 1 then D2 else D1) (h3 : T + A = Bd + R * b3) (hT : T < R) :
    (if b3 = 1 then 0 else 1) = if Spec.RsaKeyGen.absDiff c p ≤ Bd then 1 else 0 := by
  obtain eA : A = Spec.RsaKeyGen.absDiff c p := by
    unfold Spec.RsaKeyGen.absDiff
    rcases (show b1 = 0 ∨ b1 = 1 by omega_arith) with rfl | rfl <;>
      rcases (show b2 = 0 ∨ b2 = 1 by omega_arith) with rfl | rfl <;>
      simp only [hA, Nat.reduceEqDiff, ↓reduceIte] <;> split <;> omega_arith
  rw [← eA]
  obtain hAR : A < R := by rw [hA]; split <;> omega_arith
  rcases (show b3 = 0 ∨ b3 = 1 by omega_arith) with rfl | rfl
  · simp only [show ¬ (0 = 1) by decide, ↓reduceIte]; rw [ite_eq_left (by omega_arith)]
  · simp only [↓reduceIte]; rw [ite_eq_right (by omega_arith)]

theorem closeCalc_ok {s : State} {B P : Addr} {Z w c : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z)
    (hc : val32 s.mem B (slot w 0) (2 * w) = c) (hz0 : w32 s.mem B (slot w 0 + 8 * w) = 0)
    (hzP : w32 s.mem B (slot w aP + 8 * w) = 0)
    (hzB : ∀ i < w + 1, VG.Proof.Bignum.word s.mem B (slot w aBnd + 8 * i) = 0)
    (h18 : s.gpr .r18 = P) (h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * w))
    (hP : ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off P i) 1)
    (hsep : ∀ i < 8 * w, ∀ x, ofs B x < Z → off P i ≠ x) :
    WP isa (seqs closeCalc) s fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (if Spec.RsaKeyGen.absDiff c (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P (8 * w))) ≤
          2 ^ (64 * w - 100) then 1 else 0) ∧
        Env t B Z w ∧ Outside B (slot w aP) (6 * (8 * (w + 2))) s.mem t.mem) ∧ Keep ccRegs s t := by
  have hw4 := h.hw
  have hw128 := h.hw'
  have hnw := h.hs.nowrap
  obtain hn : slot w nArr ≤ 2 ^ 64 := by omega_arith
  obtain es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  obtain h35' : 256 + 35 * (8 * w) + 35 * 16 ≤ Z := by rw [← slot_lin]; exact h35
  obtain zD2 : slot w aD2 + 4 * (2 * w) ≤ Z := by rw [slot_lin]; simp only [aD2]; omega_arith
  obtain zD1 : slot w aD1 + 4 * (2 * w) ≤ Z := by rw [slot_lin]; simp only [aD1]; omega_arith
  obtain zAb : slot w aAbs + 4 * (2 * w) ≤ Z := by rw [slot_lin]; simp only [aAbs]; omega_arith
  obtain zAD2 : slot w aAbs + 4 * (2 * w) ≤ slot w aD2 ∨ slot w aD2 + 4 * (2 * w) ≤ slot w aAbs := by
    rw [slot_lin, slot_lin]; simp only [aAbs, aD2]; omega_arith
  obtain zAD1 : slot w aAbs + 4 * (2 * w) ≤ slot w aD1 ∨ slot w aD1 + 4 * (2 * w) ≤ slot w aAbs := by
    rw [slot_lin, slot_lin]; simp only [aAbs, aD1]; omega_arith
  generalize hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P (8 * w)) = p
  obtain hpR : p < 2 ^ (64 * w) := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem P (8 * w))
    rw [VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.pow256_eq, hp, show 8 * (8 * w) = 64 * w by omega_arith] at this
    exact this
  obtain hcR : c < 2 ^ (64 * w) := by
    have := val32_lt s.mem B (slot w 0) (2 * w); rw [hc, show 32 * (2 * w) = 64 * w by omega_arith] at this; exact this
  -- `p`.
  unfold closeCalc
  rw [wp_seqs (by simp)]
  refine WP.mono (loadP_ok h h35 h18 h24 hP hsep) fun t₁ ⟨⟨vP, e₁, o₁⟩, k₁⟩ => ?_
  rw [hp] at vP
  obtain c₁ : val32 t₁.mem B (slot w 0) (2 * w) = c := by rw [out_val o₁ (by decide) hn (by decide), hc]
  obtain z₁ : w32 t₁.mem B (slot w 0 + 8 * w) = 0 := by rw [out_top o₁ hn (by decide) (by decide), hz0]
  obtain zP₁ : w32 t₁.mem B (slot w aP + 8 * w) = 0 := by rw [out_top o₁ hn (by decide) (by decide), hzP]
  -- `c − p`.
  rw [wp_seqs (by simp)]
  refine WP.mono (sub_ok e₁ h35 (o := aD1) (a := 0) (b := aP) (by decide) (by decide) (by decide) (by decide)
    (by decide) z₁) fun t₂ ⟨⟨b1, hb1, v₂, r₂⟩, e₂, o₂, k₂⟩ => ?_
  rw [c₁, vP] at v₂
  have hs₂ := e₂.hs
  obtain k12 := k₁.trans k₂
  -- `r22 :=` the mask of `c < p`.
  rw [wp_seqs (by simp)]
  refine WP.mono (WP.keep [.r22] (Q := fun u => u.gpr .r22 = t₂.gpr .r20 ∧ u.mem = t₂.mem) (by
    prun []; exact BitVec.add_zero _) (by decide)) fun t₃ ⟨⟨r22₃, m₃⟩, k₃⟩ => ?_
  obtain e₃ := e₂.keep k₃ (by decide)
  obtain vP₃ : val32 t₃.mem B (slot w aP) (2 * w) = p := by rw [m₃, out_val o₂ (by decide) hn (by decide), vP]
  obtain c₃ : val32 t₃.mem B (slot w 0) (2 * w) = c := by rw [m₃, out_val o₂ (by decide) hn (by decide), c₁]
  obtain zP₃ : w32 t₃.mem B (slot w aP + 8 * w) = 0 := by rw [m₃, out_top o₂ hn (by decide) (by decide), zP₁]
  -- `p − c`.
  rw [wp_seqs (by simp)]
  refine WP.mono (sub_ok e₃ h35 (o := aD2) (a := aP) (b := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) zP₃) fun t₄ ⟨⟨b2, hb2, v₄, r₄⟩, e₄, o₄, k₄⟩ => ?_
  rw [c₃, vP₃] at v₄
  obtain d1₄ : val32 t₄.mem B (slot w aD1) (2 * w) = val32 t₂.mem B (slot w aD1) (2 * w) := by
    rw [out_val o₄ (by decide) hn (by decide), m₃]
  obtain r22₄ : t₄.gpr .r22 = BitVec.ofNat 64 0 - BitVec.ofNat 64 b1 := by
    rw [k₄.gpr _ (by decide), r22₃, r₂]
  -- `|c − p|`, the difference that does not borrow.
  rw [wp_seqs (by simp), WP.seq_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (e₄.base (rd := .r8) (by decide) (by decide) aD2) fun u₁ ⟨⟨a8, mu₁⟩, ku₁⟩ => ?_
  obtain eu₁ := e₄.keep ku₁ (by decide)
  refine WP.mono (eu₁.base (rd := .r9) (by decide) (by decide) aD1) fun u₂ ⟨⟨a9, mu₂⟩, ku₂⟩ => ?_
  obtain eu₂ := eu₁.keep ku₂ (by decide)
  refine WP.mono (eu₂.base (rd := .r5) (by decide) (by decide) aAbs) fun u₃ ⟨⟨a5, mu₃⟩, ku₃⟩ => ?_
  obtain eu₃ := eu₂.keep ku₃ (by decide)
  obtain ku13 := (ku₁.trans ku₂).trans ku₃
  refine WP.mono (WP.keep [.r20] (Q := fun u => u.gpr .r20 = u₃.gpr .r22 ∧ u.mem = u₃.mem) (by
    prun []; exact BitVec.add_zero _) (by decide)) fun u₄ ⟨⟨a20, mu₄⟩, ku₄⟩ => ?_
  obtain eu₄ := eu₃.keep ku₄ (by decide)
  obtain hmu : u₄.mem = t₄.mem := by rw [mu₄, mu₃, mu₂, mu₁]
  obtain ku14 := ku13.trans ku₄
  refine WP.mono (selectAcc_ok eu₄.hs (dA := slot w aD2) (dT := slot w aD1) (dO := slot w aAbs) (n := 2 * w)
    (b := decide (b1 = 1)) (by rw [ku₄.gpr _ (by decide), ku₃.gpr _ (by decide), ku₂.gpr _ (by decide), a8])
    (by rw [ku₄.gpr _ (by decide), ku₃.gpr _ (by decide), a9]) (by rw [ku₄.gpr _ (by decide), a5]) eu₄.h11
    (by rw [a20, ku13.gpr _ (by decide), r22₄]; rcases (show b1 = 0 ∨ b1 = 1 by omega_arith) with rfl | rfl <;> rfl)
    (by omega_arith) (by omega_arith) zD2 zD1 zAb zAD2 zAD1) fun t₅ ⟨v₅, o₅, k₅⟩ => ?_
  rw [hmu, d1₄] at v₅
  rw [hmu] at o₅
  obtain e₅ := eu₄.keep k₅ (by decide)
  -- The bound.
  obtain wB : ∀ i < w + 1, VG.Proof.Bignum.word t₅.mem B (slot w aBnd + 8 * i) = 0 := by
    intro i hi
    obtain l1 : slot w aBnd = slot w aP + 4 * (8 * (w + 2)) := by rw [slot_lin, slot_lin]; simp only [aBnd, aP]; omega_arith
    obtain hb : slot w aBnd + 8 * i + 8 ≤ Z := by rw [slot_lin]; simp only [aBnd]; omega_arith
    show word t₅.mem B (slot w aBnd + 8 * i) = 0
    rw [o₅.word (by rw [slot_lin, slot_lin]; simp only [aAbs, aBnd]; omega_arith) (by omega_arith),
      o₄.word (by rw [slot_lin, slot_lin]; simp only [aD2, aBnd]; omega_arith) (by omega_arith), m₃,
      o₂.word (by rw [slot_lin, slot_lin]; simp only [aD1, aBnd]; omega_arith) (by omega_arith),
      o₁.word (by rw [slot_lin, slot_lin]; simp only [aP, aBnd]; omega_arith) (by omega_arith)]
    exact hzB i hi
  rw [wp_seqs (by simp)]
  refine WP.mono (bound_ok e₅ h35) fun t₆ ⟨m₆, k₆⟩ => ?_
  obtain e₆ := e₅.keep k₆ (by decide)
  obtain hB2 : slot w aBnd + 8 * (w - 2) + 8 ≤ Z := by rw [slot_lin]; simp only [aBnd]; omega_arith
  obtain hBw : slot w aBnd + 8 * (w + 1) ≤ Z := by rw [slot_lin]; simp only [aBnd]; omega_arith
  obtain vB : val32 t₆.mem B (slot w aBnd) (2 * w) = 2 ^ (64 * w - 100) := by
    rw [Pre.val32_eq_wv, wv_single (k := w - 2) (v := BitVec.ofNat 64 (2 ^ 28)) (by
        show t₆.mem.readW _ 64 = _; rw [m₆, Mem.readW_writeW_self64]) w (fun i hi hik => by
        show t₆.mem.readW _ 64 = 0
        rw [m₆, Mem.readW_writeW_sep (Offset.sep B (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        exact wB i (by omega_arith)), ite_eq_left (by omega_arith)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), ← Nat.pow_add]
    congr 1; omega_arith
  obtain zB₆ : w32 t₆.mem B (slot w aBnd + 8 * w) = 0 := by
    obtain e := word_eq_w32 t₆.mem B (slot w aBnd + 8 * w)
    obtain z : word t₆.mem B (slot w aBnd + 8 * w) = 0 := by
      show t₆.mem.readW _ 64 = 0
      rw [m₆, Mem.readW_writeW_sep (Offset.sep B (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact wB w (by omega_arith)
    obtain z' : (word t₆.mem B (slot w aBnd + 8 * w)).toNat = 0 := by rw [z]; rfl
    omega_arith
  obtain vA₆ : val32 t₆.mem B (slot w aAbs) (2 * w) = val32 t₅.mem B (slot w aAbs) (2 * w) := by
    rw [m₆]
    exact (writeW_outside t₅.mem B (d := slot w aBnd + 8 * (w - 2)) _ (by omega_arith)).val32
      (by rw [slot_lin, slot_lin]; simp only [aAbs, aBnd]; omega_arith) (by omega_arith)
  -- The bound's borrow.
  rw [wp_seqs (by simp)]
  refine WP.mono (sub_ok e₆ h35 (o := aTmp) (a := aBnd) (b := aAbs) (by decide) (by decide) (by decide)
    (by decide) (by decide) zB₆) fun t₇ ⟨⟨b3, hb3, v₇, r₇⟩, e₇, o₇, k₇⟩ => ?_
  rw [vA₆, vB, v₅] at v₇
  refine WP.mono (WP.keep [.r0, .r22] (Q := fun t => t.gpr .r22 =
      (t₇.gpr .r20 &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1 ∧ t.mem = t₇.mem) (by prun []) (by decide))
    fun t ⟨⟨r22, tm⟩, kt⟩ => ?_
  obtain R := Nat.two_pow_pos (64 * w)
  obtain lt32 : ∀ (m : Mem) (j : Nat), val32 m B (slot w j) (2 * w) < 2 ^ (64 * w) := fun m j => by
    have := val32_lt m B (slot w j) (2 * w); rwa [show 32 * (2 * w) = 64 * w by omega_arith] at this
  refine ⟨⟨?_, e₇.keep kt (by decide), ?_⟩, ?_⟩
  · rw [r22, r₇, flag_final b3 hb3]
    congr 1
    exact close_math hb1 hb2 hb3 v₂ (lt32 _ _) v₄ (lt32 _ _) (by simp only [decide_eq_true_eq]) v₇ (lt32 _ _)
  · rw [tm]
    obtain l8 : 8 * w ≤ 8 * (w + 2) := Nat.mul_le_mul_left 8 (Nat.le_add_right w 2)
    obtain i1 := into_close o₁ (Nat.le_refl _) (by decide) l8
    obtain i2 := into_close o₂ (by decide) (by decide) l8
    obtain i4 := into_close o₄ (by decide) (by decide) l8
    obtain i5 := into_close o₅ (by decide) (by decide) (by rw [show 4 * (2 * w) = 8 * w by omega_arith]; exact l8)
    obtain i6 : Outside B (slot w aP) (6 * (8 * (w + 2))) t₅.mem t₆.mem := by
      rw [m₆]
      refine (writeW_outside t₅.mem B (d := slot w aBnd + 8 * (w - 2)) (BitVec.ofNat 64 (2 ^ 28)) (by omega_arith)).mono
        ?_ ?_
      · rw [slot_lin, slot_lin]; simp only [aP, aBnd]; omega_arith
      · rw [slot_lin, slot_lin]; simp only [aP, aBnd]; omega_arith
    obtain i7 := into_close o₇ (by decide) (Nat.le_refl _) l8
    exact (((((i1.trans i2).trans (by rw [← m₃]; exact i4)).trans i5).trans i6).trans i7)
  · exact (((((((((((k₁.trans k₂).trans k₃).trans k₄).trans ku₁).trans ku₂).trans ku₃).trans ku₄).trans k₅).trans
      k₆).trans k₇).trans kt).mono (by simp [ccRegs, subRegs])

end VG.Proof.RsaKeyGen.PPC64LE.Cand

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (seqs closeCalc closeCheck aP aBnd nArr)
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.Bignum (slot)

/-- `closeCheck`: `r22` is whether `c` is too close to `p`, the `p_len`
octets at `P` (none for `p_len = 0`). -/
theorem closeCheck_ok {s : State} {B P : Addr} {Z w c pL : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z)
    (hc : val32 s.mem B (slot w 0) (2 * w) = c) (hz0 : w32 s.mem B (slot w 0 + 8 * w) = 0)
    (hzP : w32 s.mem B (slot w aP + 8 * w) = 0)
    (hzB : ∀ i < w + 1, VG.Proof.Bignum.word s.mem B (slot w aBnd + 8 * i) = 0)
    (h18 : s.gpr .r18 = P) (h19 : s.gpr .r19 = BitVec.ofNat 64 pL) (hpL : pL = 0 ∨ pL = 8 * w)
    (h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * w))
    (hP : pL = 8 * w → ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off P i) 1)
    (hsep : pL = 8 * w → ∀ i < 8 * w, ∀ x, ofs B x < Z → off P i ≠ x) :
    WP isa closeCheck s fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (if Spec.RsaKeyGen.tooClose (64 * w)
          (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem P pL)) c then 1 else 0) ∧
        Env t B Z w ∧ Outside B (slot w aP) (6 * (8 * (w + 2))) s.mem t.mem) ∧ Keep ccRegs s t := by
  have hw4 := h.hw
  have hw128 := h.hw'
  unfold closeCheck
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega_arith) h19) (fun hz => ?_) (fun hz => ?_)
  · have e0 : pL = 0 := by simpa using hz
    subst e0
    refine WP.mono (WP.keep [.r22] (Q := fun t => t.gpr .r22 = 0 ∧ t.mem = s.mem) (by prun []; rfl) (by decide))
      fun t ⟨⟨t22, tm⟩, kt⟩ => ⟨⟨?_, h.keep kt (by decide), by rw [tm]; exact Outside.refl _ _ _ _⟩,
        kt.mono (by simp [ccRegs])⟩
    rw [t22]
    simp [Spec.RsaKeyGen.otherPrime, Spec.Rsa.bytesAt, Spec.RsaKeyGen.tooClose]
  · have e0 : pL = 8 * w := by simp at hz; omega_arith
    subst e0
    refine WP.mono (closeCalc_ok h h35 hc hz0 hzP hzB h18 h24 (hP rfl) (hsep rfl)) fun t ⟨⟨t22, et, ot⟩, kt⟩ =>
      ⟨⟨?_, et, ot⟩, kt⟩
    rw [t22]
    obtain hne : Spec.Rsa.bytesAt s.mem P (8 * w) ≠ [] := by
      intro e; have := congrArg List.length e
      rw [VG.Proof.Bignum.bytesAt_length] at this; simp at this; omega_arith
    simp only [Spec.RsaKeyGen.otherPrime, hne, ↓reduceIte, Spec.RsaKeyGen.tooClose, decide_eq_true_eq]

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-!
# A candidate on PPC64LE: whether a draw is at least 2

`atLeast2_ok`: `r21 := 1` if the draw `x` in array 4 is at least 2, else 0,
from `x₀ >> 1` or'ed with its other words.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (atLeast2 toThree uniform)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Proof.MillerRabin.PPC64LE (Env)

/-- Whether a word is zero, as a flag: `((a & 1) | (a >> 1)) − 1`'s top bit,
inverted. -/
theorem flag_ne0 (a : BitVec 64) :
    (((a &&& BitVec.ofNat 64 1) ||| a >>> 1) - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (if a = 0 then 0 else 1) := by
  have ha := a.isLt
  obtain e1 : (a &&& BitVec.ofNat 64 1).toNat = a.toNat % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_comm, Nat.one_and_eq_mod_two]
  obtain e2 : (a >>> 1).toNat = a.toNat / 2 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  obtain hb : ((a &&& BitVec.ofNat 64 1) ||| a >>> 1).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_or, e1, e2]; exact Nat.or_lt_two_pow (by omega_using []) (by omega_using [])
  obtain hz : ((a &&& BitVec.ofNat 64 1) ||| a >>> 1) = 0 ↔ a = 0 := by
    constructor
    · intro h
      obtain h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_or, e1, e2, show (0 : BitVec 64).toNat = 0 from rfl, Nat.or_eq_zero_iff] at h'
      exact BitVec.eq_of_toNat_eq (by simp; omega_using [h'])
    · intro h; subst h; decide
  generalize ((a &&& BitVec.ofNat 64 1) ||| a >>> 1) = b at hb hz
  obtain hb' : b = BitVec.ofNat 64 b.toNat := by simp
  rw [hb', borrow63_val hb (show 1 < 2 ^ 63 by decide)]
  by_cases h : a = 0
  · have : b.toNat = 0 := by rw [hz.mpr h]; rfl
    rw [ite_eq_left (by omega_using [this]), ite_eq_left h]; decide
  · have : b.toNat ≠ 0 := fun e => h (hz.mp (BitVec.eq_of_toNat_eq (by rw [e]; rfl)))
    rw [ite_eq_right (by omega_using [this]), ite_eq_right h]; decide

theorem or_eq_zero (a b : BitVec 64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    obtain h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, show (0 : BitVec 64).toNat = 0 from rfl, Nat.or_eq_zero_iff] at h'
    exact ⟨BitVec.eq_of_toNat_eq h'.1, BitVec.eq_of_toNat_eq h'.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem shr1_eq_zero (a : BitVec 64) : a >>> 1 = 0 ↔ a &&& (BitVec.allOnes 64 - 1) = 0 := by
  rw [VG.Proof.RsaKeyGen.and_m2_eq_zero]
  constructor
  · intro h
    obtain h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h'
    simp at h'; omega_using [h']
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp; omega_using [h]

/-- `atLeast2`: `r21 := 1` if array 4 holds at least 2, else 0. -/
theorem atLeast2_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) :
    WP isa atLeast2 s fun t =>
      (t.gpr .r21 = BitVec.ofNat 64 (if 2 ≤ wv s.mem B (slot w 4) w then 1 else 0) ∧ t.mem = s.mem ∧
        Env t B Z w) ∧ Keep [.r0, .r3, .r5, .r6, .r21] s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h.hZ
  rw [slot_lin] at hZ
  obtain s4 : slot w 4 + 8 * w ≤ Z := by rw [slot_lin]; omega_using [hZ]
  unfold atLeast2
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r5) (by decide) (by decide) 4) fun t₁ ⟨⟨a5, m₁⟩, k₁⟩ => ?_
  obtain hs₁ := hs.congr k₁.wr
  refine WP.mono (WP.keep [.r5, .r6, .r21] (Q := fun t => t.gpr .r21 = word s.mem B (slot w 4) >>> 1 ∧
      t.gpr .r5 = off B (slot w 4 + 8 * 1) ∧ t.gpr .r6 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem) ?_ (by decide))
    fun t₂ ⟨⟨b21, b5, b6, m₂⟩, k₂⟩ => ?_
  · have h11 : t₁.gpr .r11 = BitVec.ofNat 64 (2 * w) := (k₁.gpr _ (by decide)).trans h.h11
    obtain e6 : BitVec.ofNat 64 (2 * w) >>> 1 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (w - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      omega_using [hw4, hw128]
    prun [a5, h11, e6, hs₁.ld (d := slot w 4) (n := 8) (by omega_using [hw4, s4]), m₁]
  obtain k12 := k₁.trans k₂
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r21 = 0 ↔ (word s.mem B (slot w 4) >>> 1 = 0 ∧
        ∀ j, 1 ≤ j → j ≤ i → word s.mem B (slot w 4 + 8 * j) = 0)) ∧
      t.gpr .r5 = off B (slot w 4 + 8 * (i + 1)) ∧ t.mem = s.mem ∧ Keep [.r0, .r3, .r5, .r6, .r21] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .r3 .r5 0, .logic .or .r21 .r21 .r3,
      .addi .r5 .r5 8] ++ ([.subi .r6 .r6 1] : List Instr))) (cnt := .r6) (N := w - 1) (by omega_using [hw128]) (by omega_using [hw4]) Inv
    (fun i hi t ⟨tz, t5, tm, tk⟩ _ => ?_)
    ⟨by rw [b21]; exact ⟨fun e => ⟨e, fun j h1 h2 => absurd h2 (by omega_using [h1])⟩, fun e => e.1⟩, b5, m₂, k12.mono⟩ b6)
    fun t ⟨tz, _, tm, tk⟩ => ?_)
  · have hst : WP isa (.block [.load .d .r3 .r5 0, .logic .or .r21 .r21 .r3, .addi .r5 .r5 8, .subi .r6 .r6 1]) t
        fun t' => (t'.gpr .r21 = t.gpr .r21 ||| word s.mem B (slot w 4 + 8 * (i + 1)) ∧
          t'.gpr .r5 = off B (slot w 4 + 8 * (i + 1 + 1)) ∧ t'.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem) ∧ Keep [.r3, .r5, .r6, .r21] t t' := by
      refine WP.keep _ ?_ (by decide)
      prun [t5, (hs.congr tk.wr).ld (d := slot w 4 + 8 * (i + 1)) (n := 8) (by omega_using [s4, hi]), tm]
      rw [show slot w 4 + 8 * (i + 1) + 8 = slot w 4 + 8 * (i + 1 + 1) by omega_using []]
    refine WP.mono hst fun t' ⟨⟨u21, u5, u6, um⟩, uk⟩ => ⟨⟨?_, u5, um.trans tm, tk.trans' uk.mono⟩, u6⟩
    rw [u21, or_eq_zero, tz]
    constructor
    · rintro ⟨⟨e0, ej⟩, ei⟩
      refine ⟨e0, fun j h1 h2 => ?_⟩
      rcases Nat.lt_or_ge j (i + 1) with hj | hj
      · exact ej j h1 (by omega_using [hj])
      · rw [show j = i + 1 by omega_using [h2, hj]]; exact ei
    · rintro ⟨e0, ej⟩
      exact ⟨⟨e0, fun j h1 h2 => ej j h1 (by omega_using [h2])⟩, ej (i + 1) (by omega_using []) (Nat.le_refl _)⟩
  · refine WP.mono (WP.keep [.r0, .r3, .r21] (Q := fun u => u.gpr .r21 =
        (((t.gpr .r21 &&& BitVec.ofNat 64 1) ||| t.gpr .r21 >>> 1) - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1 ∧
        u.mem = t.mem) (by prun []) (by decide)) fun u ⟨⟨u21, um⟩, ku⟩ => ?_
    obtain K := tk.trans ku
    refine ⟨⟨?_, um.trans tm, h.keep K (by decide)⟩, K.mono (by simp)⟩
    rw [u21, flag_ne0]
    obtain hle := VG.Proof.RsaKeyGen.wv_le_one (m := s.mem) (p := B) (d := slot w 4) (w := w) (by omega_using [hw4])
    rw [← shr1_eq_zero] at hle
    obtain e : (t.gpr .r21 = 0) ↔ wv s.mem B (slot w 4) w ≤ 1 := by
      rw [tz, hle]
      exact ⟨fun ⟨a, b⟩ => ⟨a, fun i h1 h2 => b i h1 (by omega_using [h2])⟩, fun ⟨a, b⟩ => ⟨a, fun j h1 h2 => b j h1 (by omega_using [hw4, h2])⟩⟩
    by_cases hz : t.gpr .r21 = 0
    · rw [ite_eq_left hz, ite_eq_right (by have := e.mp hz; omega_using [this])]
    · rw [ite_eq_right hz, ite_eq_left (by have := mt e.mpr hz; omega_using [this])]

/-- `toThree`: array 4's `w` words into array 3, and its word `w` := 0. -/
theorem toThree_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) :
    WP isa toThree s fun t =>
      ((∀ i < w, word t.mem B (slot w 3 + 8 * i) = word s.mem B (slot w 4 + 8 * i)) ∧
        word t.mem B (slot w 3 + 8 * w) = 0 ∧ Outside B (slot w 3) (8 * w + 8) s.mem t.mem ∧ Env t B Z w) ∧
        Keep [.r0, .r5, .r6, .r14, .r15, .r17] s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h.hZ
  rw [slot_lin] at hZ
  unfold toThree
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r14) (by decide) (by decide) 3) fun t₁ ⟨⟨a14, m₁⟩, k₁⟩ => ?_
  obtain e₁ := h.keep k₁ (by decide)
  refine WP.mono (e₁.base (rd := .r15) (by decide) (by decide) 4) fun t₂ ⟨⟨a15, m₂⟩, k₂⟩ => ?_
  obtain e₂ := e₁.keep k₂ (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.PPC64LE.Search.copyWithin_ok e₂.hs (dS := slot w 4) (dD := slot w 3)
    a15 (by rw [k₂.gpr _ (by decide), a14]) e₂.h11 (by omega_using [hw4]) (by omega_using [hw128]) (by rw [slot_lin]; omega_using [hZ])
    (by rw [slot_lin]; omega_using [hZ]) (by rw [slot_lin, slot_lin]; omega_using [])) fun t₃ ⟨⟨_, hc, o₃⟩, k₃⟩ => ?_)
  obtain e₃ := e₂.keep k₃ (by decide)
  obtain hm2 : t₂.mem = s.mem := by rw [m₂, m₁]
  rw [WP.block_append_iff]
  refine WP.mono (e₃.base (rd := .r5) (by decide) (by decide) 3) fun t₄ ⟨⟨a5, m₄⟩, k₄⟩ => ?_
  obtain e₄ := e₃.keep k₄ (by decide)
  obtain e8 : off B (slot w 3) + BitVec.ofNat 64 (2 * w) <<< 2 = off B (slot w 3 + 8 * w) := by
    rw [show BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_using [], off_add]
  refine WP.mono (WP.keep [.r0, .r5, .r6] (Q := fun t => t.mem = t₄.mem.writeW (off B (slot w 3 + 8 * w)) (0 : BitVec 64))
    (by prun [a5, e₄.h11, e8, e₄.hs.st (d := slot w 3 + 8 * w) (n := 8) (by rw [slot_lin]; omega_using [hZ])]; rfl)
    (by decide)) fun t ⟨tm, kt⟩ => ?_
  obtain K := (((k₁.trans k₂).trans k₃).trans k₄).trans kt
  obtain wo := writeW_outside t₄.mem B (d := slot w 3 + 8 * w) (0 : BitVec 64) (by rw [slot_lin]; omega_using [hw128])
  refine ⟨⟨fun i hi => ?_, ?_, ?_, e₄.keep kt (by decide)⟩, K.mono (by simp)⟩
  · rw [tm, wo.word (by omega_using [hi]) (by rw [slot_lin]; omega_using [hw128, hi]), m₄, hc i hi, hm2]
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm, ← hm2, m₄]
    rw [m₄] at wo
    exact (o₃.mono (o' := slot w 3) (n' := 8 * w + 8) (Nat.le_refl _) (by omega_using [])).trans
      (wo.mono (o' := slot w 3) (n' := 8 * w + 8) (by omega_using []) (by omega_using []))

theorem or1_nat (a : Nat) : a ||| 1 = a + (1 - a % 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  rcases i with _ | i
  · simp [Nat.testBit_zero]; omega_using []
  · rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp
    congr 1; omega_using []

theorem mask_and1 (b : Nat) (hb : b ≤ 1) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 b) &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 b := by
  rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl <;> decide

/-- The registers `uniform` writes. -/
def uniRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r14, .r15, .r16, .r17, .r20, .r21]

/-- `uniform`: `r21 := 1` if the draw `x` in array 4 is a uniform witness for
`c` in array 0 (`2 ≤ x < c − 1`, as `x + (1 − x mod 2) < c`), else 0. -/
theorem uniform_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w) (h35 : slot w VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr ≤ Z)
    (hc : wv s.mem B (slot w 0) w = c) (hcR : c < 2 ^ (64 * w)) :
    WP isa uniform s fun t =>
      (t.gpr .r21 = BitVec.ofNat 64 (if 2 ≤ wv s.mem B (slot w 4) w ∧
          wv s.mem B (slot w 4) w + (1 - wv s.mem B (slot w 4) w % 2) < c then 1 else 0) ∧
        Env t B Z w ∧ VG.Proof.Mont.Outs B [(slot w 3, 8 * w + 8), (slot w 6, 8 * w)] s.mem t.mem) ∧ Keep uniRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h35
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr] at hZ
  rw [slot_lin] at hZ
  generalize hx : wv s.mem B (slot w 4) w = x
  unfold uniform
  refine WP.seq (WP.mono (atLeast2_ok h) fun t₁ ⟨⟨a21, m₁, e₁⟩, k₁⟩ => ?_)
  rw [hx] at a21
  refine WP.seq (WP.mono (toThree_ok e₁) fun t₂ ⟨⟨c3, z3, o₂, e₂⟩, k₂⟩ => ?_)
  rw [m₁] at c3 o₂
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (e₂.base (rd := .r5) (by decide) (by decide) 3) fun t₃ ⟨⟨a5, m₃⟩, k₃⟩ => ?_
  obtain e₃ := e₂.keep k₃ (by decide)
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.mem = t₃.mem.writeW (off B (slot w 3))
      (word t₃.mem B (slot w 3) ||| BitVec.ofNat 64 1) ∧ t.gpr .r5 = t₃.gpr .r5) (by
    prun [a5, e₃.hs.ld (d := slot w 3) (n := 8) (by rw [slot_lin]; omega_using [hZ]),
      e₃.hs.st (d := slot w 3) (n := 8) (by rw [slot_lin]; omega_using [hZ])]) (by decide)) fun t₄ ⟨⟨m₄, _⟩, k₄⟩ => ?_
  obtain e₄ := e₃.keep k₄ (by decide)
  refine WP.mono (e₄.base (rd := .r8) (by decide) (by decide) 3) fun t₅ ⟨⟨a8, m₅⟩, k₅⟩ => ?_
  obtain e₅ := e₄.keep k₅ (by decide)
  refine WP.mono (e₅.base (rd := .r9) (by decide) (by decide) 6) fun t₆ ⟨⟨a9, m₆⟩, k₆⟩ => ?_
  obtain e₆ := e₅.keep k₆ (by decide)
  obtain hm6 : t₆.mem = t₄.mem := by rw [m₆, m₅]
  obtain k16 := (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆)
  -- The numbers subtracted.
  obtain w0 : word t₃.mem B (slot w 3) = word s.mem B (slot w 4) := by
    rw [m₃]; have := c3 0 (by omega_using [hw4]); simpa using this
  obtain hA : wv t₆.mem B (slot w 3) w = x + (1 - x % 2) := by
    rw [hm6, m₄, wv_low _ _ _ _ (by omega_using [hw4]), word_writeW_self, w0]
    obtain hrest : wv (t₃.mem.writeW (off B (slot w 3)) (word s.mem B (slot w 4) ||| BitVec.ofNat 64 1)) B
        (slot w 3 + 8) (w - 1) = wv s.mem B (slot w 4 + 8) (w - 1) := by
      apply wv_shift'; intro i hi
      rw [(writeW_outside t₃.mem B (d := slot w 3) _ (by rw [slot_lin]; omega_using [hw128])).word (by omega_using [])
        (by rw [slot_lin]; omega_using [hw128, hi]), m₃,
        show slot w 3 + 8 + 8 * i = slot w 3 + 8 * (i + 1) by omega_using [],
        show slot w 4 + 8 + 8 * i = slot w 4 + 8 * (i + 1) by omega_using []]
      exact c3 (i + 1) (by omega_using [hi])
    rw [hrest]
    obtain hx' := wv_low s.mem B (slot w 4) w (by omega_using [hw4])
    rw [hx] at hx'
    rw [BitVec.toNat_or, show (BitVec.ofNat 64 1).toNat = 1 from rfl, or1_nat]
    have : (word s.mem B (slot w 4)).toNat % 2 = x % 2 := by omega_using [hx']
    omega_using [hx']
  obtain zA : VG.Proof.Mont.w32 t₆.mem B (slot w 3 + 4 * (2 * w)) = 0 := by
    obtain e := VG.Proof.Mont.word_eq_w32 t₆.mem B (slot w 3 + 8 * w)
    obtain z : VG.Proof.Mont.word t₆.mem B (slot w 3 + 8 * w) = 0 := by
      show t₆.mem.readW _ 64 = 0
      rw [hm6, m₄, Mem.readW_writeW_sep (Offset.sep B (by omega_using [hw4]) (by rw [slot_lin]; omega_using [hw128])
        (by rw [slot_lin]; omega_using [hw128])) (by decide), m₃]
      exact z3
    obtain z' : (VG.Proof.Mont.word t₆.mem B (slot w 3 + 8 * w)).toNat = 0 := by rw [z]; rfl
    rw [show slot w 3 + 4 * (2 * w) = slot w 3 + 8 * w by omega_using []]
    omega_using [e, z']
  obtain hM : wv t₆.mem B (slot w 0) w = c := by
    rw [← hc, hm6, m₄, ← Pre.val32_eq_wv, ← Pre.val32_eq_wv]
    rw [(VG.Proof.Mont.writeW_outside t₃.mem B (d := slot w 3) _ (by rw [slot_lin]; omega_using [hw128])).val32 (by rw [slot_lin, slot_lin]; omega_using [])
      (by rw [slot_lin]; omega_using [hw128]), m₃, VG.Proof.Mont.Outside.val32 o₂ (by rw [slot_lin, slot_lin]; omega_using [])
      (by rw [slot_lin]; omega_using [hw128])]
  refine WP.seq (WP.mono (subMod_ok e₆.hs (dA := slot w 3) (dT := slot w 6) (dM := slot w 0) (n := 2 * w)
    (by rw [k₆.gpr _ (by decide), a8]) a9 e₆.h10 e₆.h11 (by omega_using [hw4]) (by omega_using [hw128]) (by rw [slot_lin]; omega_using [hZ])
    (by rw [slot_lin]; omega_using [hZ]) (by rw [slot_lin]; omega_using [hZ]) (by rw [slot_lin, slot_lin]; omega_using [])
    (by rw [slot_lin, slot_lin]; omega_using [])) fun t₇ ⟨⟨b, hb, v₇, r₇⟩, o₇, k₇⟩ => ?_)
  rw [zA] at r₇
  simp only [Pre.val32_eq_wv] at v₇
  rw [hA, hM, show 32 * (2 * w) = 64 * w by omega_using []] at v₇
  refine WP.mono (WP.keep [.r0, .r3, .r21] (Q := fun t => t.gpr .r21 = t₇.gpr .r21 &&& (t₇.gpr .r20 &&&
      BitVec.ofNat 64 1) ∧ t.mem = t₇.mem) (by prun []) (by decide)) fun t ⟨⟨t21, tm⟩, kt⟩ => ?_
  obtain K := (k16.trans k₇).trans kt
  obtain hD := VG.Proof.Mont.val32_lt t₇.mem B (slot w 6) (2 * w)
  rw [Pre.val32_eq_wv, show 32 * (2 * w) = 64 * w by omega_using []] at hD
  obtain bi := (borrow_iff hb v₇ hD hcR).1
  refine ⟨⟨?_, ⟨hs.congr K.wr, ?_, ?_, ?_, ?_, hw4, hw128, h.hZ⟩, ?_⟩, K.mono (by simp [uniRegs])⟩
  · have r21₇ : t₇.gpr .r21 = t₁.gpr .r21 :=
      ((((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).gpr .r21 (by decide))
    rw [t21, r₇, show (if 0 < b then 1 else 0) = b by rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl <;> rfl,
      mask_and1 b hb, r21₇, a21]
    by_cases h2 : 2 ≤ x
    · rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl
      · rw [ite_eq_left h2, ite_eq_right (fun hh => absurd (bi.mpr hh.2) (by decide))]; decide
      · rw [ite_eq_left h2, ite_eq_left ⟨h2, bi.mp rfl⟩]; decide
    · rw [ite_eq_right h2, ite_eq_right (fun hh => h2 hh.1)]
      rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl <;> decide
  · rw [K.gpr _ (by decide)]; exact h.h10
  · rw [K.gpr _ (by decide)]; exact h.h29
  · rw [K.gpr _ (by decide)]; exact h.h11
  · rw [K.gpr _ (by decide)]; exact h.h31
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hy
    rw [tm, o₇ y (by omega_using [hy]), hm6, m₄, VG.Proof.Mont.writeW_outside t₃.mem B (d := slot w 3) _
      (by rw [slot_lin]; omega_using [hw128]) y (by omega_using [hy]), m₃, o₂ y hy.1]

end VG.Proof.RsaKeyGen.PPC64LE.Cand
