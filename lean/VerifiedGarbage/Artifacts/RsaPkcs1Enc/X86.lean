module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndVerified
public import VerifiedGarbage.TCB.X86.Print

/-! # RSAES-PKCS1-v1_5 encryption with a precomputed public key, and from a random tape, on x86 -/

@[expose] public section
namespace VG.Artifacts.RsaPkcs1Enc.X86
open VG.Proof.RsaPkcs1Sig.X86.Ver (baseline)

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact VG.X86.target {
    code := Impl.RsaPkcs1Enc.X86.Random.code Proof.RsaPkcs1Enc.X86.Rnd.encName (Proof.RsaPkcs1Enc.X86.Rnd.enc baseline)
    stack := Proof.RsaPkcs1Enc.X86.Rnd.stackBytes
    verified := Proof.RsaPkcs1Enc.X86.Rnd.code_verified Proof.RsaPkcs1Enc.X86.Rnd.encName baseline
    spSafe := Proof.RsaPkcs1Enc.X86.Rnd.code_sp Proof.RsaPkcs1Enc.X86.Rnd.encName baseline }]

end VG.Artifacts.RsaPkcs1Enc.X86
