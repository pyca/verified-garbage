module

public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CT
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Correct

/-! # FFDH key-generation attempts on x86-64: verified -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.Ffdh.X86_64.Domain

theorem gk_verified (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) :
    Verified target (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.code M.mm E.code (.seq (.block r2Head) R.code))
      (Spec.Ffdh.generateKeyContract abi) := by
  exact Verified.of_correct (gk_correct M E R hmx) (gk_constantTime M E R hE) gk_implies

end VG.Proof.Ffdh.X86_64.GenerateKey
