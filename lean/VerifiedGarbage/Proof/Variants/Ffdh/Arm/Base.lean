module

public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyVerified

/-! Baseline ARMv7 FFDH with RSA's fixed-window arithmetic. -/

@[expose] public section
namespace VG.Proof.Variants.Ffdh.Arm.Base

def variant : VG.Proof.Ffdh.Arm.Backend where
  checkDomain := VG.Impl.Ffdh.Arm.Domain.CheckDomain.code
  checkDomain_verified := VG.Proof.Ffdh.Arm.domain_verified
  checkPublic := VG.Impl.Ffdh.Arm.Domain.CheckPublic.code
  checkPublic_verified := VG.Proof.Ffdh.Arm.checkPublic_verified
  checkPrivate := VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code
  checkPrivate_verified := VG.Proof.Ffdh.Arm.private_verified
  exchange := VG.Impl.Ffdh.Arm.Domain.Exchange.code
  exchange_verified := VG.Proof.Ffdh.Arm.exchange_verified
  generateKey := VG.Impl.Ffdh.Arm.Domain.GenerateKey.code
  generateKey_verified := VG.Proof.Ffdh.Arm.key_verified
  keyStack := by decide +kernel
  suffix := ""
  features := []

end VG.Proof.Variants.Ffdh.Arm.Base
