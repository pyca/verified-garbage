module

public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.CT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Correct

/-! # FFDH private-key validation on x86-64: verified -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain

theorem kp_verified (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) :
    Verified target (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code))
      (Spec.Ffdh.checkPrivateContract abi) := by
  exact Verified.of_correct (kp_correct M E R hmx) (kp_constantTime M E R hE) kp_implies

end VG.Proof.Ffdh.X86_64.CheckPrivate
