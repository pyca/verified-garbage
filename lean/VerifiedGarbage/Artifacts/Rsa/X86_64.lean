module

public import VerifiedGarbage.Impl.Rsa.X86_64.Fn
public import VerifiedGarbage.Proof.Rsa.X86_64.Instances
public import VerifiedGarbage.TCB.X86_64.Print

/-! # RSA (RFC 8017) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Rsa.X86_64

open VG.Proof.Rsa.X86_64.Scrubbed

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.publicPrecompute, verified := publicPrecompute_scrubbed, spSafe := publicPrecompute_spSafe },
  Spec.Rsa.publicPrecomputeApi.artifact X86_64.target { suffix := "_adx", code := Impl.Rsa.X86_64.Fn.publicPrecomputeAdx, verified := publicPrecomputeAdx_scrubbed, spSafe := publicPrecomputeAdx_spSafe },
  Spec.Rsa.privatePrecomputeApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.privatePrecompute, verified := privatePrecompute_scrubbed, spSafe := privatePrecompute_spSafe },
  Spec.Rsa.privatePrecomputeApi.artifact X86_64.target { suffix := "_adx", code := Impl.Rsa.X86_64.Fn.privatePrecomputeAdx, verified := privatePrecomputeAdx_scrubbed, spSafe := privatePrecomputeAdx_spSafe },
  Spec.Rsa.crtValuesApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.crtValues, verified := crtValues_scrubbed, spSafe := crtValues_spSafe },
  Spec.Rsa.recoverPrimesDetApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.recoverPrimesDet, verified := recoverPrimesDet_scrubbed, spSafe := recoverPrimesDet_spSafe },
  Spec.Rsa.checkKeyApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.checkKey, verified := checkKey_scrubbed, spSafe := checkKey_spSafe }]

end VG.Artifacts.Rsa.X86_64
