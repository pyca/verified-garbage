module

public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.CT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Correct

/-! # FFDH domain validation on x86-64: verified -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain

theorem cd_verified (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) :
    Verified target (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.code M.mm E.code (.seq (.block r2Head) R.code))
      (Spec.Ffdh.checkDomainContract abi) := by
  exact Verified.of_correct (cd_correct M E R hmx) (cd_constantTime M E R hE) cd_implies

end VG.Proof.Ffdh.X86_64.CheckDomain
