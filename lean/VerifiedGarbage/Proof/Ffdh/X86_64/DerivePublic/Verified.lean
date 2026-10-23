module

public import VerifiedGarbage.Impl.Ffdh.X86_64.DerivePublic
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.CT
import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Correct

/-! # FFDH public-value derivation on x86-64: verified -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain

theorem dv_verified (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) :
    Verified target (VG.Impl.Ffdh.X86_64.Domain.DerivePublic.code M.mm E.code (.seq (.block r2Head) R.code))
      (Spec.Ffdh.derivePublicContract abi) := by
  exact Verified.of_correct (dv_correct M E R hmx) (dv_constantTime M E R hE) dv_implies

end VG.Proof.Ffdh.X86_64.DerivePublic
