module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeInputs

/-! # Only six signature arguments determine precomputation resources -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86

theorem PrecomputeInputs.argsEq {base : Addr} {bytes len : Nat} {args other : Nat → BitVec 32} {s : State}
    (H : PrecomputeInputs base bytes len args s) (eq : ∀ i < 6, args i = other i) :
    PrecomputeInputs base bytes len other s := by
  have H0 := eq 0 (by decide)
  have H1 := eq 1 (by decide)
  have H2 := eq 2 (by decide)
  have H3 := eq 3 (by decide)
  have H4 := eq 4 (by decide)
  have H5 := eq 5 (by decide)
  refine ⟨H.scratch, H.lower, H.upper, H.space, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, H.room, H.top,
    by rw [← H4]; exact H.hbase, by rw [← H5]; exact H.hbytes, H.argWrite, by rw [← H2]; exact H.nArg, by rw [← H0]; exact H.outArgs, H.spScratch,
    by rw [← H0]; exact H.spOut⟩
  · intro i hi; rw [← eq i hi]; exact H.stack i hi
  · rw [← H1]; exact H.preLen
  · rw [← H3]; exact H.nLen
  · rw [← H0]; exact H.outFit
  · rw [← H2]; exact H.nFit
  · rw [← H0]; exact H.outWrite
  · rw [← H2]; exact H.nRead
  · rw [← H0]; exact H.outApart
  · rw [← H2]; exact H.nApart

end VG.Proof.Bignum.X86
