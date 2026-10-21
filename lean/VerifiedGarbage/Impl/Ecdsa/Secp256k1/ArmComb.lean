module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-! Shared signing and key-generation pipelines with the fixed-base comb. -/

@[expose] public section
namespace VG.Impl.Ecdsa.Arm

def signSecp256k1Comb : Prog VG.Arm.isa := secp256k1.signWith Weierstrass.Arm.mulGeneratorSecp256k1

def publicKeySecp256k1Comb : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith secp256k1 Weierstrass.Arm.mulGeneratorSecp256k1

def verifySecp256k1Comb : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith secp256k1 Weierstrass.Arm.mulGeneratorSecp256k1

end VG.Impl.Ecdsa.Arm
