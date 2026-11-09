module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LEComb
public import VerifiedGarbage.Proof.EcKey.PPC64LE.Secp256k1.Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.Secp256k1
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.PPC64LE.Secp256k1.CombLit
public import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Law

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcSecp256k1.PPC64LE

open VG.Proof.Secp256k1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeySecp256k1Comb
    verified := Proof.EcKey.PPC64LE.Secp256k1.combPk_verified hasLaw.law }]

end VG.Artifacts.EcSecp256k1.PPC64LE
