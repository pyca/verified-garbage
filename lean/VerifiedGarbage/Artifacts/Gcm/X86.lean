module

public import VerifiedGarbage.Proof.Gcm.X86.Ghash
public import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Ghash
public import VerifiedGarbage.Proof.Framework.Registration

/-! # GHASH on x86 -/

@[expose] public section

namespace VG.Artifacts.Gcm.X86

def artifacts : List Artifact := [
  Spec.Gcm.ghashApi.artifact X86.target {
    code := Impl.Gcm.X86.ghash
    verified := Proof.Gcm.X86.ghash_verified },
  Spec.Gcm.ghashApi.artifact X86.target {
    suffix := "_pclmul"
    features := ["pclmulqdq", "ssse3"]
    code := Impl.Gcm.X86.Pclmul.ghash
    stack := 0
    verified := Proof.Gcm.X86.Pclmul.ghash_verified }]

end VG.Artifacts.Gcm.X86
