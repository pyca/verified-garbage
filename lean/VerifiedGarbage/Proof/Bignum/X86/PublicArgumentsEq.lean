module

public import VerifiedGarbage.Proof.Bignum.X86.PublicInputs

/-! # Only the ten signature arguments determine public-call resources -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86

theorem PublicInputs.argsEq {base : Addr} {bytes len : Nat} {args other : Nat → BitVec 32} {s : State}
    (H : PublicInputs base bytes len args s) (eq : ∀ i < 10, args i = other i) :
    PublicInputs base bytes len other s := by
  have H0 := eq 0 (by decide)
  have H1 := eq 1 (by decide)
  have H2 := eq 2 (by decide)
  have H3 := eq 3 (by decide)
  have H4 := eq 4 (by decide)
  have H5 := eq 5 (by decide)
  have H6 := eq 6 (by decide)
  have H7 := eq 7 (by decide)
  refine ⟨H.scratch, H.lower, H.upper, H.space, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [← eq i hi]; exact H.stack i hi
  · rw [← H1]; exact H.outLen
  · rw [← H3]; exact H.nLen
  · rw [← H7]; exact H.inLen
  · rw [← H5]; exact H.ePositive
  · rw [← H5]; exact H.eBound
  · rw [← H0]; exact H.outFit
  · rw [← H2]; exact H.nFit
  · rw [← H4, ← H5]; exact H.eFit
  · rw [← H6]; exact H.inFit
  · rw [← H0]; exact H.outWrite
  · rw [← H2]; exact H.nRead
  · rw [← H4, ← H5]; exact H.eRead
  · rw [← H6]; exact H.inRead
  · rw [← H0]; exact H.outApart
  · rw [← H2]; exact H.nApart
  · rw [← H4, ← H5]; exact H.eApart
  · rw [← H6]; exact H.inApart

end VG.Proof.Bignum.X86
