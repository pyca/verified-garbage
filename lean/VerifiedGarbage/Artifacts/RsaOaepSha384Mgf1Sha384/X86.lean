module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha512
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances

/-! # RSAES-OAEP with SHA-384 and MGF1 with SHA-384 on x86: encryption -/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha384Mgf1Sha384.X86

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha384 Spec.Mgf1.sha384).artifact X86.target {
    code := Proof.RsaOaep.X86.Enc.encryptCode Proof.RsaOaep.X86.sha384 Proof.RsaOaep.X86.sha384 Proof.RsaPkcs1Sig.X86.Ver.baseline
    stack := Proof.RsaOaep.X86.Enc.stackBytes
    verified := Proof.RsaOaep.X86.Enc.encrypt_verified Proof.RsaOaep.X86.sha384 Proof.RsaOaep.X86.sha384
      (Proof.RsaOaep.X86.Enc.encrypt_sat_sha384 _) Proof.RsaPkcs1Sig.X86.Ver.baseline
    spSafe := Proof.RsaOaep.X86.Enc.code_sp Proof.RsaOaep.X86.sha384 Proof.RsaOaep.X86.sha384 Proof.RsaPkcs1Sig.X86.Ver.baseline }]

end VG.Artifacts.RsaOaepSha384Mgf1Sha384.X86
