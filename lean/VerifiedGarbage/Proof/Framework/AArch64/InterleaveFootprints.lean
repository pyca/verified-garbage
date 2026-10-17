module

public import VerifiedGarbage.Proof.Framework.AArch64.Interleave
public import VerifiedGarbage.Proof.Framework.Interleave

/-!
# AArch64: the footprints of `Interleave.lean`, as an instance of the generic framework

The footprints of `Proof/Framework/AArch64/Interleave.lean` (memory at
`[xb, #off]`), as `VG.Interleave.Footprints isa`, so that AArch64 code uses
the ISA-generic `Interleave.Footprints.indeps_of_check`, `Interleave.WP.merge`
and `Interleave.WP.weave` (with `Impl.Weave.weave`) as x86-64 code does.
-/

@[expose] public section

namespace VG.AArch64.Interleave

theorem indep_union_left {xb : Reg} {A B C : Fp} (h : (A.union B).indep xb C = true) :
    A.indep xb C = true ∧ B.indep xb C = true := by
  simp only [Fp.indep, Fp.union, Nat.and_or_distrib_right, Nat.and_or_distrib_left, Nat.or_eq_zero_iff,
    Nat.shiftRight_or_distrib, Nat.testBit_or, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, Bool.or_eq_false_iff] at h ⊢
  grind

theorem indep_union_right {xb : Reg} {A B C : Fp} (h : A.indep xb (B.union C) = true) :
    A.indep xb B = true ∧ A.indep xb C = true := by
  simp only [Fp.indep, Fp.union, Nat.and_or_distrib_right, Nat.and_or_distrib_left, Nat.or_eq_zero_iff,
    Nat.shiftRight_or_distrib, Nat.testBit_or, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, Bool.or_eq_false_iff] at h ⊢
  grind

/-- The footprints of the class, for memory at `[xb, #off]`. -/
def footprints (xb : Reg) : VG.Interleave.Footprints isa where
  Fp := Fp
  fp := fp xb
  Inv _ := True
  preserves _ _ _ _ _ := trivial
  empty := .empty
  union := Fp.union
  indep := Fp.indep xb
  indep_union_left := indep_union_left
  indep_union_right := indep_union_right
  comm hx hy h s _ := exec_comm hx hy (Indep.of h) s

end VG.AArch64.Interleave
