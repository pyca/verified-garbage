module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees

/-! Public constructions reuse the public implementation carried by each RSA backend. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm

def pdOfCrt (v : CrtImpl) : Proof.RsaPkcs1Sig.Arm.PdImpl where
  name := v.pdName
  code := v.pd
  verified := v.pdVerified
  stack := v.pdStack

end VG.Proof.Rsa.Arm
