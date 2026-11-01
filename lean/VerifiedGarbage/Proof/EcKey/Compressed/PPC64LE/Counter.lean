module

import VerifiedGarbage.Impl.Weierstrass.PPC64LE
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.PPC64LE.Loop
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# SEC 1 point decompression on PPC64LE: the descent's counters

P-224's descent keeps two counters in `r31`, which the calls keep: the
round's `j` in its high word and the squarings' `i` in its low one,
`r31 = 2³² j + i` (`ctr`). `loopBy_ok` runs a loop whose condition reads an
index of an invariant; the lemmas below evaluate the conditions and the
instructions that move the counters.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE

/-- The counters `j` and `i` in `r31`. -/
abbrev ctr (j i : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ 32 * j + i)

/-- A loop whose body takes the invariant from `j` to `j - 1`, with the
loop's condition `j ≠ 0` in the invariant, run from `n ≥ 1`. -/
theorem loopBy_ok {body : Prog isa} {cond : Cond} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hc : ∀ j s, Inv j s → isa.eval cond s = some (decide (j ≠ 0)))
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s → WP isa body s fun s' => Inv (j - 1) s')
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) {s : State} (hs : Inv n s) :
    WP isa (.loop body cond) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' hi' => ?_
  have he := hc _ _ hi'
  by_cases hj : j - 1 = 0
  · exact .inl ⟨by rw [he]; simp [hj], hQ s' (by rw [hj] at hi'; exact hi')⟩
  · exact .inr ⟨by rw [he]; simp [hj], j - 1, by omega, by omega, by omega, hi'⟩

theorem ctr_lo (j i : Nat) : (ctr j i).setWidth 32 = BitVec.ofNat 32 i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat32_eq_zero {i : Nat} (hi : i < 2 ^ 32) : (BitVec.ofNat 32 i = 0) = (i = 0) := by
  apply propext
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] at this
  · rintro rfl; rfl

/-- The low word's test. -/
theorem eval_lo_nonzero {s : State} {j i : Nat} (hi : i < 2 ^ 32) (h : s.gpr .r31 = ctr j i) :
    isa.eval (.nonzero .w .r31) s = some (decide (i ≠ 0)) := by
  simp only [eval, State.read, Size.bits, h, ctr_lo j i, Option.some.injEq]
  by_cases hi0 : i = 0
  · subst hi0; rfl
  · have : BitVec.ofNat 32 i ≠ 0 := by rw [ne_eq, ofNat32_eq_zero hi]; exact hi0
    exact (bne_iff_ne.mpr this).trans (decide_eq_true hi0).symm

theorem eval_lo_zero {s : State} {j i : Nat} (hi : i < 2 ^ 32) (h : s.gpr .r31 = ctr j i) :
    isa.eval (.zero .w .r31) s = some (decide (i = 0)) := by
  simp only [eval, State.read, Size.bits, h, ctr_lo j i, Option.some.injEq]
  by_cases hi0 : i = 0
  · subst hi0; rfl
  · have : BitVec.ofNat 32 i ≠ 0 := by rw [ne_eq, ofNat32_eq_zero hi]; exact hi0
    rw [decide_eq_false hi0]; exact beq_eq_false_iff_ne.mpr this

/-- The whole register's test, with the low word zero. -/
theorem eval_hi_nonzero {s : State} {j : Nat} (hj : j < 2 ^ 32) (h : s.gpr .r31 = ctr j 0) :
    isa.eval (.nonzero .d .r31) s = some (decide (j ≠ 0)) := by
  rw [eval_nonzero_ofNat h (by omega)]
  by_cases hj0 : j = 0
  · simp [hj0]
  · simp only [Nat.add_zero, Option.some.injEq, decide_eq_decide]; omega

/-- `r31 -= 1` takes the low word down. -/
theorem ctr_dec {j i : Nat} (hi : 1 ≤ i) (hi' : i < 2 ^ 32) :
    ctr j i - BitVec.ofNat 64 1 = ctr j (i - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `r4 = r31 >>> 32` is the high word. -/
theorem ctr_hi {j i : Nat} (hj : j < 2 ^ 32) (hi : i < 2 ^ 32) : ctr j i >>> 32 = BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  omega

/-- `r31 |= i` sets the low word, when it is zero. -/
theorem ctr_or {j i : Nat} (hj : j < 2 ^ 32) (hi : i < 2 ^ 32) :
    ctr j 0 ||| BitVec.ofNat 64 i = ctr j i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.add_zero,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.two_pow_add_eq_or_of_lt hi]

/-- `r31 -= 1 <<< 32` takes the high word down, with the low one zero. -/
theorem ctr_next {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 32) :
    ctr j 0 - BitVec.ofNat 64 1 <<< 32 = ctr (j - 1) 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `r31 = 95 <<< 32`. -/
theorem ctr_init (j : Nat) : BitVec.ofNat 64 j <<< 32 = ctr j 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

end VG.Proof.EcKey.Compressed.PPC64LE
