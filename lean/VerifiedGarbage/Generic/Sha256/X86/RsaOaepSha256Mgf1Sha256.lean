module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha256
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances

/-! # RSAES-OAEP with SHA-256 and MGF1 with SHA-256 on x86: encryption, for each Sha256 backend -/

@[expose] public section

namespace VG.Generic.Sha256.X86.RsaOaepSha256Mgf1Sha256

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha256 Spec.Mgf1.sha256).artifact X86.target {
    suffix := v.stream.suffix
    code := Proof.RsaOaep.X86.Enc.encryptCode (Proof.RsaOaep.X86.sha256 v) (Proof.RsaOaep.X86.sha256 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    stack := Proof.RsaOaep.X86.Enc.stackBytes
    verified := Proof.RsaOaep.X86.Enc.encrypt_verified (Proof.RsaOaep.X86.sha256 v) (Proof.RsaOaep.X86.sha256 v)
      (Proof.RsaOaep.X86.Enc.encrypt_sat_sha256 _) Proof.RsaPkcs1Sig.X86.Ver.baseline
    spSafe := Proof.RsaOaep.X86.Enc.code_sp (Proof.RsaOaep.X86.sha256 v) (Proof.RsaOaep.X86.sha256 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    features := v.features }]

end VG.Generic.Sha256.X86.RsaOaepSha256Mgf1Sha256
