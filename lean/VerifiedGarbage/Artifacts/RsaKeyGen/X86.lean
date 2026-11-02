module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Safety
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Inverse
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Safety

/-! # Native RSA key generation on baseline i686 -/

@[expose] public section
namespace VG.Artifacts.RsaKeyGen.X86

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact X86.target {
    stack := 68
    code := Impl.RsaKeyGen.X86.KeyRuntime.code
    verified := Proof.RsaKeyGen.X86.KeyRuntime.verified
    spSafe := Proof.RsaKeyGen.X86.KeyRuntime.code_sp }]

end VG.Artifacts.RsaKeyGen.X86
