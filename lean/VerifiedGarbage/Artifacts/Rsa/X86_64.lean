module

public import VerifiedGarbage.Impl.Rsa.X86_64.Fn
public import VerifiedGarbage.Proof.Rsa.X86_64.Instances
public import VerifiedGarbage.TCB.X86_64.Print

/-! # RSA (RFC 8017) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Rsa.X86_64

open VG.Proof.Rsa.X86_64.Scrubbed

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.publicPrecompute, verified := Proof.Rsa.X86_64.Scrubbed.publicPrecompute_scrubbed, spSafe := Proof.Rsa.X86_64.Scrubbed.publicPrecompute_spSafe },
  Spec.Rsa.publicPrecomputeApi.artifact X86_64.target { suffix := "_adx", code := Impl.Rsa.X86_64.Fn.publicPrecomputeAdx, verified := Proof.Rsa.X86_64.Scrubbed.publicPrecomputeAdx_scrubbed, spSafe := Proof.Rsa.X86_64.Scrubbed.publicPrecomputeAdx_spSafe },
  Spec.Rsa.privatePrecomputeApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.privatePrecompute, verified := Proof.Rsa.X86_64.Scrubbed.privatePrecompute_scrubbed, spSafe := Proof.Rsa.X86_64.Scrubbed.privatePrecompute_spSafe },
  Spec.Rsa.privatePrecomputeApi.artifact X86_64.target { suffix := "_adx", code := Impl.Rsa.X86_64.Fn.privatePrecomputeAdx, verified := Proof.Rsa.X86_64.Scrubbed.privatePrecomputeAdx_scrubbed, spSafe := Proof.Rsa.X86_64.Scrubbed.privatePrecomputeAdx_spSafe },
  Spec.Rsa.crtValuesApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.crtValues, verified := Proof.Rsa.X86_64.Scrubbed.crtValues_scrubbed, spSafe := Proof.Rsa.X86_64.Scrubbed.crtValues_spSafe },
  Spec.Rsa.recoverPrimesDetApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.recoverPrimesDet, verified := Proof.Rsa.X86_64.Scrubbed.recoverPrimesDet_scrubbed, spSafe := Proof.Rsa.X86_64.Scrubbed.recoverPrimesDet_spSafe },
  Spec.Rsa.checkKeyApi.artifact X86_64.target { code := Impl.Rsa.X86_64.Fn.checkKey, verified := Proof.Rsa.X86_64.Scrubbed.checkKey_scrubbed, spSafe := Proof.Rsa.X86_64.Scrubbed.checkKey_spSafe }]

end VG.Artifacts.Rsa.X86_64
