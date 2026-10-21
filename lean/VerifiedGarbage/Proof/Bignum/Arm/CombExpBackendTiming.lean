module

import VerifiedGarbage.Proof.Bignum.Arm.CombExpChooseCT
import VerifiedGarbage.Proof.Bignum.Arm.CombExpPhaseCT
import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackendCT
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernelAt
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackend
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpTiming
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpTiming

/-! Every RSA Montgomery backend supports independent secret comb exponents. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm

theorem backendTiming (backend : MontBackend) (base source table sp : BitVec 32)
    (len w bytes M g N : Nat) (bs1 bs2 : List Byte)
    (length1 : bs1.length=bytes) (length2 : bs2.length=bytes)
    (widthBound : N≤8*bytes) (size : bytes<2^32)
    (scheduleFit : 6*Spec.Rsa.FixedBaseComb.rows N<2^31) (widthFit : N<2^31)
    (scalarFit1 : Spec.Rsa.os2ip bs1<2^N) (scalarFit2 : Spec.Rsa.os2ip bs2<2^N) :
    Timing (kernelAt backend base source table sp len w bytes M g N bs1 length1 widthBound size scheduleFit widthFit scalarFit1)
      (kernelAt backend base source table sp len w bytes M g N bs2 length2 widthBound size scheduleFit widthFit scalarFit2) := by
  refine ⟨rfl,?_,?_⟩
  · intro o a b ho ha hb
    exact (arithmetic_ct backend base source table sp len w M g N bs1 o a b ho ha hb).mono
      (fun _ _ h => ⟨⟨h.1.1,h.1.2.1.1,h.1.2.2⟩,
        ⟨h.2.1.1,h.2.1.2.1.1,h.2.1.2.2⟩,h.2.2⟩) (fun _ _ h => h)
  · intro i E1 E2 hi
    exact choose_ct backend base source table sp len w bytes N M g E1 E2 i bs1 bs2 length1 length2
      widthBound size scheduleFit widthFit scalarFit1 scalarFit2 hi

end VG.Proof.Bignum.Arm.CombExp
