module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecP.Verified
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on x86 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.X86

def direct : List Artifact := [
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact VG.X86.target Proof.RsaPkcs1Enc.X86.Scrub.encryptRandomReg]

end VG.Artifacts.RsaPkcs1Enc.X86

-- RSAES-PKCS1-v1_5 decryption with implicit rejection on x86
namespace VG.Artifacts.RsaPkcs1Enc.X86.Sha256RsaPrivateCrt

open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Backend) (c : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact X86.target {
    suffix := qualifiedName "" [("sha256", v.stream.suffix), ("crt", c.suffix)]
    code := Proof.RsaPkcs1Enc.X86.Dec.decryptCodeP v c Proof.Rsa.X86.PrivChecked.crtPBaseline
    verified := .unscrubbed (Proof.RsaPkcs1Enc.X86.Dec.decryptPrecomputed_verified v c)
    spSafe := Proof.RsaPkcs1Enc.X86.Dec.codeP_sp v c Proof.Rsa.X86.PrivChecked.crtPBaseline }]

end VG.Artifacts.RsaPkcs1Enc.X86.Sha256RsaPrivateCrt

namespace VG.Artifacts.RsaPkcs1Enc.X86

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.Sha256.X86.variants.flatMap fun v => VG.Proof.Variants.RsaPrivateCrt.X86.variants.flatMap fun v2 => Sha256RsaPrivateCrt.artifacts v v2)

end VG.Artifacts.RsaPkcs1Enc.X86
