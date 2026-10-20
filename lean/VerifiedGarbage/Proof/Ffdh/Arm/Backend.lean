module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.CallF

/-! A verified native FFDH backend, including the attempt called by its
retry controller. Callers inherit every implementation's feature requirements. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

structure Backend where
  checkDomain : Prog isa
  checkDomain_verified : Verified target checkDomain (Spec.Ffdh.checkDomainContract abi 128)
  checkPublic : Prog isa
  checkPublic_verified : Verified target checkPublic (Spec.Ffdh.checkPublicContract abi 128)
  checkPrivate : Prog isa
  checkPrivate_verified : Verified target checkPrivate (Spec.Ffdh.checkPrivateContract abi 128)
  exchange : Prog isa
  exchange_verified : Verified target exchange (Spec.Ffdh.exchangeContract abi 128)
  generateKey : Prog isa
  generateKey_verified : Verified target generateKey (Spec.Ffdh.generateKeyContract abi 128)
  keyStack : FrameStack.armStack generateKey ≤ 128
  suffix : String
  features : List String

def Backend.keyName (b : Backend) : String := Spec.Ffdh.generateKeyApi.name ++ b.suffix

end VG.Proof.Ffdh.Arm
