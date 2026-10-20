module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.CallF

/-! A callable key-generation attempt for the native rejection controller.
The arithmetic implementation is supplied generically by its Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

structure KeyBackend where
  generateKey : Prog isa
  generateKey_verified : Verified target generateKey (Spec.Ffdh.generateKeyContract abi 176)
  keyStack : FrameStack.armStack generateKey ≤ 176
  suffix : String
  features : List String

def KeyBackend.keyName (b : KeyBackend) : String := Spec.Ffdh.generateKeyApi.name ++ b.suffix

end VG.Proof.Ffdh.Arm
