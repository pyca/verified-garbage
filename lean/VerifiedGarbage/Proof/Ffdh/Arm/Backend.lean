module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.CallF

/-! A verified native FFDH backend, for domain/key validation and exchange. Callers inherit every implementation's feature requirements. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

structure Backend where
  checkDomain : Prog isa
  checkDomain_verified : Verified target checkDomain (Spec.Ffdh.checkDomainContract (abi.withConsts VG.Impl.Ffdh.Arm.VettedGroups.tableConsts) 128)
  checkPublic : Prog isa
  checkPublic_verified : Verified target checkPublic (Spec.Ffdh.checkPublicContract abi 128)
  checkPrivate : Prog isa
  checkPrivate_verified : Verified target checkPrivate (Spec.Ffdh.checkPrivateContract abi 128)
  exchange : Prog isa
  exchange_verified : Verified target exchange (Spec.Ffdh.exchangeContract abi 128)
  suffix : String
  features : List String

end VG.Proof.Ffdh.Arm
