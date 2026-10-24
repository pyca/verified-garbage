module

public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeVerified

/-! Baseline ARMv7 FFDH with RSA's fixed-window arithmetic. -/

@[expose] public section
namespace VG.Proof.Variants.Ffdh.Arm.Base

def variant : VG.Proof.Ffdh.Arm.Backend where
  checkDomain := VG.Impl.Ffdh.Arm.VettedValidation.code
  checkDomain_verified := VG.Proof.Ffdh.Arm.VettedValidation.verified
  checkPublic := VG.Impl.Ffdh.Arm.Domain.CheckPublic.code
  checkPublic_verified := VG.Proof.Ffdh.Arm.checkPublic_verified
  checkPrivate := VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code
  checkPrivate_verified := VG.Proof.Ffdh.Arm.private_verified
  exchange := VG.Impl.Ffdh.Arm.Domain.Exchange.code
  exchange_verified := VG.Proof.Ffdh.Arm.exchange_verified
  suffix := ""
  features := []

end VG.Proof.Variants.Ffdh.Arm.Base
