module

public import VerifiedGarbage.Proof.Gcm.X86.Ghash
public import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Ghash
public import VerifiedGarbage.Proof.Framework.Registration

/-! # GHASH on x86 -/

@[expose] public section

namespace VG.Artifacts.Gcm.X86

def artifacts : List Artifact := [
  Spec.Gcm.ghashApi.artifact X86.target {
    notes := ["`•` is computed bit by bit as Algorithm 1 of §6.3 does, with masks instead of \
        branches."]
    code := Impl.Gcm.X86.ghash
    verified := Proof.Gcm.X86.ghash_verified },
  Spec.Gcm.ghashApi.artifact X86.target {
    suffix := "_pclmul"
    features := ["pclmulqdq", "ssse3"]
    notes := ["PCLMULQDQ multiplication with SSSE3 byte reversal, processing one block at a time. \
        The implementation retains the accumulator and transformed hash key in SSE registers and \
        does not use the scratch buffer."]
    code := Impl.Gcm.X86.Pclmul.ghash
    stack := 0
    verified := Proof.Gcm.X86.Pclmul.ghash_verified }]

end VG.Artifacts.Gcm.X86
