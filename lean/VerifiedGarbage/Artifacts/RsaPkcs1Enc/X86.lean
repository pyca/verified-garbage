module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcVerified

/-! # RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86 -/

@[expose] public section
namespace VG.Artifacts.RsaPkcs1Enc.X86
open VG.Proof.RsaPkcs1Sig.X86.Ver (baseline)

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact VG.X86.target {
    code := Impl.RsaPkcs1Enc.X86.Precomputed.code baseline.name baseline.code
    stack := Proof.RsaPkcs1Enc.X86.Pc.stackBytes
    verified := Proof.RsaPkcs1Enc.X86.Pc.code_verified baseline
    spSafe := Proof.RsaPkcs1Enc.X86.Pc.code_sp baseline }]

end VG.Artifacts.RsaPkcs1Enc.X86
