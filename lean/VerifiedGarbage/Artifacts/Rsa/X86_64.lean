module

public import VerifiedGarbage.Impl.Rsa.X86_64.Fn
public import VerifiedGarbage.Proof.Rsa.X86_64.Scrubbed
public import VerifiedGarbage.TCB.X86_64.Print

/-! # RSA (RFC 8017) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Rsa.X86_64

open VG.Proof.Rsa.X86_64.Scrubbed

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.publicPrecompute, verified := .scrubbed publicPrecompute_scrubbed, spSafe := publicPrecompute_spSafe },
  Spec.Rsa.publicPrecomputeApi.artifact X86_64.target { suffix := "_adx", code := Impl.Rsa.X86_64.Fn.publicPrecomputeAdx, verified := .scrubbed publicPrecomputeAdx_scrubbed, spSafe := publicPrecomputeAdx_spSafe },
  Spec.Rsa.privatePrecomputeApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.privatePrecompute, verified := .scrubbed privatePrecompute_scrubbed, spSafe := privatePrecompute_spSafe },
  Spec.Rsa.privatePrecomputeApi.artifact X86_64.target { suffix := "_adx", code := Impl.Rsa.X86_64.Fn.privatePrecomputeAdx, verified := .scrubbed privatePrecomputeAdx_scrubbed, spSafe := privatePrecomputeAdx_spSafe },
  Spec.Rsa.crtValuesApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.crtValues, verified := .scrubbed crtValues_scrubbed, spSafe := crtValues_spSafe },
  Spec.Rsa.recoverPrimesDetApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.recoverPrimesDet, verified := .scrubbed recoverPrimesDet_scrubbed, spSafe := recoverPrimesDet_spSafe },
  Spec.Rsa.checkKeyApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.checkKey, verified := .scrubbed checkKey_scrubbed, spSafe := checkKey_spSafe }]

end VG.Artifacts.Rsa.X86_64
