module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSA (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rsa.PPC64LE

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.Fn.publicPrecompute
    verified := .scrubbed Proof.Rsa.PPC64LE.Scrub.publicPrecompute_scrubbed },
  Spec.Rsa.privatePrecomputeApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.Fn.privatePrecompute
    verified := .scrubbed Proof.Rsa.PPC64LE.Scrub.privatePrecompute_scrubbed },
  Spec.Rsa.crtValuesApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.Fn.crtValues
    verified := .scrubbed Proof.Rsa.PPC64LE.Scrub.crtValues_scrubbed },
  Spec.Rsa.checkKeyApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.Fn.checkKey
    verified := .scrubbed Proof.Rsa.PPC64LE.Scrub.checkKey_scrubbed },
  Spec.Rsa.recoverPrimesDetApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.Fn.recoverPrimesDet
    verified := .scrubbed Proof.Rsa.PPC64LE.Scrub.recoverPrimesDet_scrubbed }]

end VG.Artifacts.Rsa.PPC64LE
