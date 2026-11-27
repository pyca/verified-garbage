module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Frame
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Verified
import VerifiedGarbage.Proof.Rc2.X86_64.Key
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Chained
import VerifiedGarbage.Proof.Rc2.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC2 on x86-64 -/

namespace VG.Artifacts.Rc2.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Rc2.cbcInitApi.artifact X86_64.target {
    code := Impl.Rc2.X86_64.Fn.cbcInit
    verified := Proof.Rc2.X86_64.Scrub.cbcInit_scrubbed },
  Spec.Rc2.cbcEncryptChainedApi.artifact X86_64.target {
    code := Impl.Rc2.X86_64.Fn.cbcEncryptChained
    verified := Proof.Rc2.X86_64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Rc2.cbcDecryptChainedApi.artifact X86_64.target {
    code := Impl.Rc2.X86_64.Fn.cbcDecryptChained
    verified := Proof.Rc2.X86_64.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Rc2.X86_64
