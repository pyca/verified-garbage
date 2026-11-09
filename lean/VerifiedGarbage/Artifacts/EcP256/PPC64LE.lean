module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LEComb
public import VerifiedGarbage.Proof.EcKey.PPC64LE.P256Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.PPC64LE.P256CombLit
public import VerifiedGarbage.Proof.P256.PPC64LE.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P256.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P256.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P256.Lit

/-! # P-256 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP256.PPC64LE

open VG.Proof.P256.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressP256
    verified := Proof.EcKey.Compressed.PPC64LE.P256.compress_verified },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressP256
    verified := Proof.EcKey.Compressed.PPC64LE.P256.decompress_verified hasLaw.law },
  Spec.EcKey.P256.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyP256Comb
    verified := Proof.EcKey.PPC64LE.combPk_verified hasLaw.law }]

end VG.Artifacts.EcP256.PPC64LE
