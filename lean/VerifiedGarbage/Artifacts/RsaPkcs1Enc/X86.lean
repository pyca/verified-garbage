module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndVerified
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecVerified
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86

/-! # RSAES-PKCS1-v1_5 encryption with a precomputed public key, and from a random tape, on x86 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.X86
open VG.Proof.RsaPkcs1Sig.X86.Ver (baseline)

def direct : List Artifact := [
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact VG.X86.target {
    code := Impl.RsaPkcs1Enc.X86.Random.code Proof.RsaPkcs1Enc.X86.Rnd.encName (Proof.RsaPkcs1Enc.X86.Rnd.enc baseline)
    stack := Proof.RsaPkcs1Enc.X86.Rnd.stackBytes
    verified := Proof.RsaPkcs1Enc.X86.Rnd.code_verified Proof.RsaPkcs1Enc.X86.Rnd.encName baseline
    spSafe := Proof.RsaPkcs1Enc.X86.Rnd.code_sp Proof.RsaPkcs1Enc.X86.Rnd.encName baseline }]

end VG.Artifacts.RsaPkcs1Enc.X86

-- RSAES-PKCS1-v1_5 decryption with implicit rejection on x86
namespace VG.Artifacts.RsaPkcs1Enc.X86.Sha256RsaPrivateCrt

open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Backend) (c : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.decryptApi.artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha256", v.stream.suffix), ("crt", c.suffix)]
    code := Proof.RsaPkcs1Enc.X86.Dec.decryptCode v c
    stack := Proof.RsaPkcs1Enc.X86.Dec.stackBytes
    verified := Proof.RsaPkcs1Enc.X86.Dec.code_verified v c
    spSafe := Proof.RsaPkcs1Enc.X86.Dec.code_sp v c
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Artifacts.RsaPkcs1Enc.X86.Sha256RsaPrivateCrt

namespace VG.Artifacts.RsaPkcs1Enc.X86

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.Sha256.X86.variants.flatMap fun v => VG.Proof.Variants.RsaPrivateCrt.X86.variants.flatMap fun v2 => Sha256RsaPrivateCrt.artifacts v v2)

end VG.Artifacts.RsaPkcs1Enc.X86
