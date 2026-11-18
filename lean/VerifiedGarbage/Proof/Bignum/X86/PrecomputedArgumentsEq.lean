module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputs
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPair
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.ExponentCheckTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Bignum.X86.PrecomputedFailureTiming`, which the modules that import this one used -/

section

/-! # Invalid public keys clear a public-length output with a fixed trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86

theorem precomputedFailure_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PrecomputedPair base bytes len args) PublicFn.failure (fun _ _ => True) := by
  have Zero : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block [.mov .eax (.imm 0)])
      (VG.X86.Taint.Agree loadTaint) := checkedProgramChange (hint := .block []) rfl rfl
  have Head := VG.RelCT.block_append (VG.RelCT.seq (loadArguments_relCT 0 1 (args 0) (args 1)) Zero)
  have Loop : RelCT isa (VG.X86.Taint.Agree loadTaint) (.loop (.block PublicFn.clearStep) .ne)
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h)
      (hc := VG.Taint.hintOf taint loadTaint (.loop (.block PublicFn.clearStep) .ne))
    rfl
  apply (VG.RelCT.seq Head Loop).mono
  · intro s t H
    exact ⟨H.agree, (H.left.stack 0 (by decide)).readSrc, (H.right.stack 0 (by decide)).readSrc,
      (H.left.stack 1 (by decide)).readSrc, (H.right.stack 1 (by decide)).readSrc⟩
  · exact fun _ _ h => h

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.PrecomputedExponentTiming`, which the modules that import this one used -/

section

/-! # Public exponent argument loading and scanning share a common trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem precomputedExponent_trace {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (H : PrecomputedPair base bytes len args s t)
    (same : Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat =
      Spec.Rsa.bytesAt t.mem (byteAddr (args 4)) (args 5).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa PublicFn.scanExponent s tr sf) (F : Exec isa PublicFn.scanExponent t ur tf) : tr = ur := by
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (loadArguments_relCT 4 5 (args 4) (args 5) _ _ _ _ _ _
        ⟨H.agree, (H.left.stack 4 (by decide)).readSrc, (H.right.stack 4 (by decide)).readSrc,
          (H.left.stack 5 (by decide)).readSrc, (H.right.stack 5 (by decide)).readSrc⟩ E1 F1).1
      obtain ⟨Ps, Cs, Ms, Ks⟩ := wp_result (argumentPair_ok (by decide) (by decide)
        (H.left.stack 4 (by decide)).readSrc (H.left.stack 5 (by decide)).readSrc) E1
      obtain ⟨Pt, Ct, Mt, Kt⟩ := wp_result (argumentPair_ok (by decide) (by decide)
        (H.right.stack 4 (by decide)).readSrc (H.right.stack 5 (by decide)).readSrc) F1
      have T2 := exponentCheck_trace (ep := args 4)
        (eb := Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)
        (by rw [bytesAt_length]; exact H.left.ePositive)
        (by rw [bytesAt_length]; exact (args 5).isLt)
        (by rw [bytesAt_length]; exact H.left.eFit)
        (by rw [bytesAt_length, Ks.2.1, Ks.2.2]; exact H.left.eRead)
        (by rw [bytesAt_length, Kt.2.1, Kt.2.2]; exact H.right.eRead)
        (by intro i hi; rw [Ms]; simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range])
        (by
          intro i hi
          rw [Mt]
          have Eq := List.getElem_of_eq same hi
          simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] using Eq.symm)
        Ps Pt (by rw [bytesAt_length, BitVec.ofNat_toNat]; exact Cs)
        (by rw [bytesAt_length, BitVec.ofNat_toNat]; exact Ct) E2 F2
      rw [T1, T2]

end VG.Proof.Bignum.X86

end

end

/-! # Only the ten signature arguments determine public-call resources -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86

theorem PrecomputedInputs.argsEq {base : Addr} {bytes len : Nat} {args other : Nat → BitVec 32} {s : State}
    (H : PrecomputedInputs base bytes len args s) (eq : ∀ i < 10, args i = other i) :
    PrecomputedInputs base bytes len other s := by
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
  · rw [← H3]; exact H.preLen
  · rw [← H7]; exact H.inLen
  · rw [← H5]; exact H.ePositive
  · rw [← H5]; exact H.eBound
  · rw [← H0]; exact H.outFit
  · rw [← H2]; exact H.preFit
  · rw [← H4, ← H5]; exact H.eFit
  · rw [← H6]; exact H.inFit
  · rw [← H0]; exact H.outWrite
  · rw [← H2]; exact H.preRead
  · rw [← H4, ← H5]; exact H.eRead
  · rw [← H6]; exact H.inRead
  · rw [← H0]; exact H.outApart
  · rw [← H2]; exact H.preApart
  · rw [← H4, ← H5]; exact H.eApart
  · rw [← H6]; exact H.inApart

end VG.Proof.Bignum.X86
