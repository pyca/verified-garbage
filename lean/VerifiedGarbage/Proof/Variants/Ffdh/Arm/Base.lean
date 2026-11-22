module

public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! Baseline ARMv7 FFDH with RSA's fixed-window arithmetic. -/

@[expose] public section
namespace VG.Proof.Variants.Ffdh.Arm.Base

def variant : VG.Proof.Ffdh.Arm.Backend where
  checkPublic := VG.Impl.Ffdh.Arm.Domain.CheckPublic.code
  checkPublic_verified := VG.Proof.Ffdh.Arm.checkPublic_verified
  exchange := VG.Impl.Ffdh.Arm.Domain.Exchange.code
  exchange_verified := VG.Proof.Ffdh.Arm.exchange_verified
  suffix := ""
  features := []

end VG.Proof.Variants.Ffdh.Arm.Base
