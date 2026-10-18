module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptStackSafety
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # i686 precomputed PKCS #1 encryption -/

@[expose] public section
namespace VG.Artifacts.RsaPkcs1Enc.X86
open VG.Proof.RsaPkcs1Enc.X86.Enc
open VG.Proof.RsaPkcs1Sig.X86.Ver (baseline)

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact VG.X86.target {
    code := Impl.RsaPkcs1Enc.X86.Encrypt.code baseline.name baseline.code
    stack := encryptStack
    verified := encrypt_verified baseline
    spSafe := code_sp baseline }]

end VG.Artifacts.RsaPkcs1Enc.X86
