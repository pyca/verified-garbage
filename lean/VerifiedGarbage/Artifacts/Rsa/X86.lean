module

public import VerifiedGarbage.Proof.Rsa.X86.Scrub
public import VerifiedGarbage.Impl.Rsa.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # RSA (RFC 8017) on x86 -/

@[expose] public section
namespace VG.Artifacts.Rsa.X86

def artifacts : List Artifact := [
  Spec.Rsa.recoverPrimesDetApi.artifact X86.target {
    code := Impl.Rsa.X86.Fn.recoverPrimesDet
    verified := .scrubbed Proof.Rsa.X86.Scrub.recoverPrimesDet_scrubbed },
  Spec.Rsa.checkKeyApi.artifact X86.target {
    code := Impl.Rsa.X86.Fn.checkKey
    verified := .scrubbed Proof.Rsa.X86.Scrub.checkKey_scrubbed },
  Spec.Rsa.crtValuesApi.artifact X86.target {
    code := Impl.Rsa.X86.Fn.crtValues
    verified := .scrubbed Proof.Rsa.X86.Scrub.crtValues_scrubbed },
  Spec.Rsa.publicPrecomputeApi.artifact X86.target {
    code := Impl.Rsa.X86.Fn.publicPrecompute
    verified := .scrubbed Proof.Rsa.X86.Scrub.publicPrecompute_scrubbed },
  Spec.Rsa.privatePrecomputeApi.artifact X86.target {
    code := Impl.Rsa.X86.Fn.privatePrecompute
    verified := .scrubbed Proof.Rsa.X86.Scrub.privatePrecompute_scrubbed }]

end VG.Artifacts.Rsa.X86
