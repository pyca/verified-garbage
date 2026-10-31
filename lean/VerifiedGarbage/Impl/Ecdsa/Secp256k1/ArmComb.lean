module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm

/-! Shared signing and key-generation pipelines with the fixed-base comb. -/

@[expose] public section
namespace VG.Impl.Ecdsa.Arm

def signSecp256k1CombWith (u : Bool) : Prog VG.Arm.isa :=
  (secp256k1With u).signWith (Weierstrass.Arm.mulGeneratorSecp256k1With u)

def signSecp256k1Comb : Prog VG.Arm.isa := signSecp256k1CombWith false

def signSecp256k1CombU : Prog VG.Arm.isa := signSecp256k1CombWith true

def publicKeySecp256k1CombWith (u : Bool) : Prog VG.Arm.isa :=
  EcKey.Arm.Cfg.publicKeyWith (secp256k1With u) (Weierstrass.Arm.mulGeneratorSecp256k1With u)

def publicKeySecp256k1Comb : Prog VG.Arm.isa := publicKeySecp256k1CombWith false

def publicKeySecp256k1CombU : Prog VG.Arm.isa := publicKeySecp256k1CombWith true

def verifySecp256k1CombWith (u : Bool) : Prog VG.Arm.isa :=
  Verify.Arm.Cfg.verifyWith (secp256k1With u) (Weierstrass.Arm.mulGeneratorSecp256k1With u)

def verifySecp256k1Comb : Prog VG.Arm.isa := verifySecp256k1CombWith false

def verifySecp256k1CombU : Prog VG.Arm.isa := verifySecp256k1CombWith true

end VG.Impl.Ecdsa.Arm
