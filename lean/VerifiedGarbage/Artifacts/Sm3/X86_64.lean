module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Impl.Sm3.X86_64.Fn
import VerifiedGarbage.Proof.Sm3.X86_64.Shared
import VerifiedGarbage.Proof.Sm3.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm3.X86_64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM3 (GB/T 32905-2016) on x86-64 -/

namespace VG.Artifacts.Sm3.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Sm3.initApi.artifact X86_64.target { code := Impl.Sm3.X86_64.Fn.init, verified := Proof.Sm3.X86_64.init_scrubbed, spSafe := Proof.Sm3.X86_64.init_spSafe },
  Spec.Sm3.updateApi.artifact X86_64.target { code := Impl.Sm3.X86_64.Fn.update, verified := Proof.Sm3.X86_64.update_scrubbed, spSafe := Proof.Sm3.X86_64.update_spSafe },
  Spec.Sm3.finalizeApi.artifact X86_64.target { code := Impl.Sm3.X86_64.Fn.finalize, verified := Proof.Sm3.X86_64.finalize_scrubbed, spSafe := Proof.Sm3.X86_64.finalize_spSafe }]

spec_apis artifacts

end VG.Artifacts.Sm3.X86_64
