module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA on PPC64LE: range masks

In a working space (`Env`) with the modulus in array 0:

* `subLt_ok`: `r20 :=` the mask of `[a] < [0]` (`subMod`'s borrow into array
  3), for an array `a` whose word `w` is zero;
* `inRange_ok`: `r22 &=` the mask of `0 < [a] < [0]`, with 0 in array 7.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

theorem mask_and (a b : Bool) : mask a &&& mask b = mask (a && b) := by
  cases a <;> cases b <;> rfl

theorem mask_clear (a b : Bool) : (mask a ||| mask b) ^^^ mask b = mask (a && !b) := by
  cases a <;> cases b <;> rfl

theorem mask_of_ite (p : Prop) [Decidable p] :
    BitVec.ofNat 64 0 - BitVec.ofNat 64 (if p then 1 else 0) = mask (decide p) := by
  by_cases h : p <;> simp [h, mask]

theorem slot_eq (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := rfl

/-- The registers `subLt` writes. -/
def subLtRegs : List Reg := [.r0, .r3, .r8, .r9, .r14, .r15, .r16, .r17, .r20]

/-- `[a] < [0]` as `subMod`'s borrow, into `r20` as a mask; array 3 changes. -/
theorem subLt_ok {s : State} {B : Addr} {Z w a : Nat} (h : Env s B Z w) (ha : a < 28)
    (ha3 : a ≠ 3) (top : word s.mem B (slot w a + 8 * w) = 0) {c : Prog isa}
    {Q : State → Prop}
    (hc : ∀ t, t.gpr .r20 = mask (decide (arr s.mem B w a < arr s.mem B w 0)) →
      Outside B (slot w 3) (8 * (w + 2)) s.mem t.mem → Keep subLtRegs s t → WP isa c t Q) :
    WP isa (.seq (.block (PublicChecked.base .r8 a ++ PublicChecked.base .r9 3)) (.seq subMod c)) s Q := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e3 := slot_eq w 3; have ea := slot_eq w a; have e28 := slot_eq w 28
  have hA := h.arr ha
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r8) (by decide) (by decide) a) fun s₁ ⟨⟨a8, m1⟩, k1⟩ => ?_
  have e1 := h.keep k1 (by decide)
  refine WP.mono (e1.base (rd := .r9) (by decide) (by decide) 3) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  have sep3 := slot_sep (w := w) ha3
  refine WP.seq (WP.mono (subMod_ok (dA := slot w a) (dT := slot w 3) (dM := slot w 0) (n := 2 * w)
    (hs.congr k12.wr) ((k2.gpr .r8 (by decide)).trans a8) a9 ((k12.gpr .r10 (by decide)).trans h.h10)
    ((k12.gpr .r11 (by decide)).trans h.h11) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)) fun t ⟨⟨c', hc', hv, h20⟩, ot, kt⟩ => ?_)
  rw [hm2] at hv h20 ot
  refine hc t ?_ (ot.mono (Nat.le_refl _) (by omega)) ((k12.trans kt).mono (by decide))
  have hw32 : w32 s.mem B (slot w a + 4 * (2 * w)) = 0 := by
    have := word_eq_w32 s.mem B (slot w a + 8 * w)
    rw [top, show (0 : BitVec 64).toNat = 0 from rfl] at this
    rw [show slot w a + 4 * (2 * w) = slot w a + 8 * w by omega]; omega
  have hlt : (w32 s.mem B (slot w a + 4 * (2 * w)) < c') ↔ arr s.mem B w a < arr s.mem B w 0 := by
    have hT := val32_lt t.mem B (slot w 3) (2 * w)
    have hA' := val32_lt s.mem B (slot w a) (2 * w)
    have hM := val32_lt s.mem B (slot w 0) (2 * w)
    simp only [arr]
    rw [hw32]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc' with rfl | rfl
    · omega
    · rw [show 32 * (2 * w) = 64 * w by omega] at hT hv hA' hM; omega
  rw [h20, mask_of_ite]
  simp only [hlt]

/-- The registers `inRange` writes. -/
def inRangeRegs : List Reg := subLtRegs ++ [.r4, .r19, .r22]

/-- `inRange a`: `r22 &=` the mask of `0 < [a] < [0]`, with 0 in array 7 and
`[a]`'s word `w` zero; array 3 changes. -/
theorem inRange_ok {s : State} {B : Addr} {Z w a : Nat} {b : Bool} (h : Env s B Z w) (ha : a < 28)
    (ha3 : a ≠ 3) (top : word s.mem B (slot w a + 8 * w) = 0) (h7 : arr s.mem B w 7 = 0)
    (h22 : s.gpr .r22 = mask b) :
    WP isa (inRange a) s fun t =>
      (t.gpr .r22 = mask (b && decide (0 < arr s.mem B w a ∧ arr s.mem B w a < arr s.mem B w 0)) ∧
        Outside B (slot w 3) (8 * (w + 2)) s.mem t.mem) ∧ Keep inRangeRegs s t := by
  unfold inRange
  refine subLt_ok h ha ha3 top fun s₁ h20 o1 k1 => ?_
  have e1 := h.keep k1 (by decide)
  have hn : slot w 28 ≤ 2 ^ 64 := by have := h.hs.nowrap; have := h.hZ; omega
  have q1 : ∀ j, j < 28 → j ≠ 3 → arr s₁.mem B w j = arr s.mem B w j := fun j hj h3 =>
    Outside.arrEq o1 hj h3 hn
  refine WP.seq (WP.mono (eqMask_ok e1 .r19 (a := a) (b := 7) ha (by decide)) fun s₂ ⟨⟨a19, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.mono (WP.keep [.r20, .r22] (Q := fun t => t.gpr .r22 = mask (b && decide
      (0 < arr s.mem B w a ∧ arr s.mem B w a < arr s.mem B w 0)) ∧ t.mem = s₂.mem) ?_ (by decide))
    fun t ⟨⟨t26, tm⟩, kt⟩ => ⟨⟨t26, by rw [tm, m2]; exact o1⟩, (k12.trans kt).mono (by decide)⟩
  have b20 : s₂.gpr .r20 = mask (decide (arr s.mem B w a < arr s.mem B w 0)) :=
    (k2.gpr .r20 (by decide)).trans h20
  have b22 : s₂.gpr .r22 = mask b := (k12.gpr .r22 (by decide)).trans h22
  rw [← arr, ← arr, q1 a ha ha3, q1 7 (by decide) (by decide), h7] at a19
  unfold clear19
  prun [b20, b22, a19, mask_clear, mask_and]
  congr 1
  cases b <;> by_cases h0 : arr s.mem B w a = 0 <;> by_cases hl : arr s.mem B w a < arr s.mem B w 0 <;>
    simp [h0, hl] <;> omega

end VG.Proof.Dsa.PPC64LE
