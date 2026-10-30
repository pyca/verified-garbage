module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Hashes.Sha512
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Verified
public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances

/-!
# RSAES-OAEP with SHA-512/256 and MGF1 with SHA-512/256 on x86: encryption

It uses 208 bytes of stack: the push of the registers (16 bytes), its frame
(144 bytes) and the 48 bytes of its calls': the hash functions', and the 44
of `vg_rsa_public_precomputed_checked`.
-/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha512_256Mgf1Sha512_256.X86

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha512_256 Spec.Mgf1.sha512_256).artifact X86.target {
    code := Proof.RsaOaep.X86.Enc.encryptCode Proof.RsaOaep.X86.sha512_256 Proof.RsaOaep.X86.sha512_256 Proof.RsaPkcs1Sig.X86.Ver.baseline
    stack := Proof.RsaOaep.X86.Enc.stackBytes
    verified := Proof.RsaOaep.X86.Enc.encrypt_verified Proof.RsaOaep.X86.sha512_256 Proof.RsaOaep.X86.sha512_256
      (Proof.RsaOaep.X86.Enc.encrypt_sat_sha512_256 _) Proof.RsaPkcs1Sig.X86.Ver.baseline
    spSafe := Proof.RsaOaep.X86.Enc.code_sp Proof.RsaOaep.X86.sha512_256 Proof.RsaOaep.X86.sha512_256 Proof.RsaPkcs1Sig.X86.Ver.baseline }]

end VG.Artifacts.RsaOaepSha512_256Mgf1Sha512_256.X86
