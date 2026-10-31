module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha1
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha512
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances

/-! # RSAES-OAEP with SHA-512 and MGF1 with SHA-1 on x86: encryption, for each Sha1 backend -/

@[expose] public section

namespace VG.Generic.Sha1.X86.RsaOaepSha512Mgf1Sha1

def artifacts (v : Proof.Sha1.X86.Variants.Backend) : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha512 Spec.Mgf1.sha1).artifact X86.target {
    suffix := v.stream.suffix
    code := Proof.RsaOaep.X86.Enc.encryptCode Proof.RsaOaep.X86.sha512 (Proof.RsaOaep.X86.sha1 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    stack := Proof.RsaOaep.X86.Enc.stackBytes
    verified := Proof.RsaOaep.X86.Enc.encrypt_verified Proof.RsaOaep.X86.sha512 (Proof.RsaOaep.X86.sha1 v)
      (Proof.RsaOaep.X86.Enc.encrypt_sat_sha512 _) Proof.RsaPkcs1Sig.X86.Ver.baseline
    spSafe := Proof.RsaOaep.X86.Enc.code_sp Proof.RsaOaep.X86.sha512 (Proof.RsaOaep.X86.sha1 v) Proof.RsaPkcs1Sig.X86.Ver.baseline
    features := v.features }]

end VG.Generic.Sha1.X86.RsaOaepSha512Mgf1Sha1
