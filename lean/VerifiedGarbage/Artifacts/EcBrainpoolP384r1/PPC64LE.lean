module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LEComb
public import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP384r1.Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP384r1.CombLit
public import VerifiedGarbage.Proof.BrainpoolP384r1.PPC64LE.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1.Lit

/-! # brainpoolP384r1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP384r1.PPC64LE

open VG.Proof.BrainpoolP384r1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyBrainpoolP384r1Comb
    verified := Proof.EcKey.PPC64LE.BrainpoolP384r1.combPk_verified hasLaw.law },
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP384r1
    verified := Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1.compress_verified },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP384r1
    verified := Proof.EcKey.Compressed.PPC64LE.BrainpoolP384r1.decompress_verified hasLaw.law }]

end VG.Artifacts.EcBrainpoolP384r1.PPC64LE
