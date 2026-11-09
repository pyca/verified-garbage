module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LEComb
public import VerifiedGarbage.Proof.EcKey.PPC64LE.P224.Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.PPC64LE.P224.CombLit
public import VerifiedGarbage.Proof.P224.PPC64LE.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.P224.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P224.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P224.Lit

/-! # P-224 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP224.PPC64LE

open VG.Proof.P224.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressP224
    verified := Proof.EcKey.Compressed.PPC64LE.P224.compress_verified },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressP224
    verified := Proof.EcKey.Compressed.PPC64LE.P224.decompress_verified hasLaw.law },
  Spec.EcKey.P224.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyP224Comb
    verified := Proof.EcKey.PPC64LE.P224.combPk_verified hasLaw.law }]

end VG.Artifacts.EcP224.PPC64LE
