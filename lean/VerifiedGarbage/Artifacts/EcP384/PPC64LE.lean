module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LEComb
public import VerifiedGarbage.Proof.EcKey.PPC64LE.P384.Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.PPC64LE.P384.CombLit
public import VerifiedGarbage.Proof.P384.PPC64LE.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P384.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P384.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P384.Lit

/-! # P-384 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP384.PPC64LE

open VG.Proof.P384.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressP384
    verified := Proof.EcKey.Compressed.PPC64LE.P384.compress_verified },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressP384
    verified := Proof.EcKey.Compressed.PPC64LE.P384.decompress_verified hasLaw.law },
  Spec.EcKey.P384.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyP384Comb
    verified := Proof.EcKey.PPC64LE.P384.combPk_verified hasLaw.law }]

end VG.Artifacts.EcP384.PPC64LE
