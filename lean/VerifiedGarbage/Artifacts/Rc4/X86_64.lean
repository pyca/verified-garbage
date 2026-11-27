module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Impl.Rc4.X86_64.Fn
import VerifiedGarbage.Proof.Rc4.X86_64.Verified
import VerifiedGarbage.Proof.Rc4.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc4.X86_64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC4 on x86-64 -/

namespace VG.Artifacts.Rc4.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Rc4.initApi.artifact X86_64.target { code := Impl.Rc4.X86_64.Fn.init, verified := Proof.Rc4.X86_64.Scrub.init_scrubbed, spSafe := Proof.Rc4.X86_64.Scrub.init_spSafe },
  Spec.Rc4.applyApi.artifact X86_64.target { code := Impl.Rc4.X86_64.Fn.apply, verified := Proof.Rc4.X86_64.Scrub.apply_scrubbed, spSafe := Proof.Rc4.X86_64.Scrub.apply_spSafe }]

spec_apis artifacts

end VG.Artifacts.Rc4.X86_64
