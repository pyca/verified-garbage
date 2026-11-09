module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LEComb
public import VerifiedGarbage.Proof.EcKey.PPC64LE.P521.Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.PPC64LE.P521.CombLit
public import VerifiedGarbage.Proof.P521.PPC64LE.Law

/-! # P-521 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP521.PPC64LE

open VG.Proof.P521.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P521.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyP521Comb
    verified := Proof.EcKey.PPC64LE.P521.combPk_verified hasLaw.law }]

end VG.Artifacts.EcP521.PPC64LE
