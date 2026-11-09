module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP512r1.Lit
public import VerifiedGarbage.Proof.BrainpoolP512r1.PPC64LE.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP512r1.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.BrainpoolP512r1.Lit

/-! # brainpoolP512r1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP512r1.PPC64LE

open VG.Proof.BrainpoolP512r1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.publicKeyBrainpoolP512r1
    verified := Proof.EcKey.PPC64LE.BrainpoolP512r1.pk_verified hasLaw.law },
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP512r1
    verified := Proof.EcKey.Compressed.PPC64LE.BrainpoolP512r1.compress_verified },
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP512r1
    verified := Proof.EcKey.Compressed.PPC64LE.BrainpoolP512r1.decompress_verified hasLaw.law }]

end VG.Artifacts.EcBrainpoolP512r1.PPC64LE
