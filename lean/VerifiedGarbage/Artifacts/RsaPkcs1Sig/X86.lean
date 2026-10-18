module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackSafety
public import VerifiedGarbage.Proof.Framework.Registration

/-! # i686 public PKCS #1 signature operations -/

@[expose] public section
namespace VG.Artifacts.RsaPkcs1Sig.X86
open VG.Proof.RsaPkcs1Sig.X86.Ver

def artifacts : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact VG.X86.target {
    code := Impl.RsaPkcs1Sig.X86.Verify.code baseline.name baseline.code
    stack := verifyStack
    verified := verify_verified baseline
    spSafe := code_sp baseline },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact VG.X86.target {
    code := Impl.RsaPkcs1Sig.X86.Recover.code baseline.name baseline.code
    stack := Proof.RsaPkcs1Sig.X86.Rcv.recoverStack
    verified := Proof.RsaPkcs1Sig.X86.Rcv.recover_verified baseline
    spSafe := Proof.RsaPkcs1Sig.X86.Rcv.code_sp baseline }]

end VG.Artifacts.RsaPkcs1Sig.X86
