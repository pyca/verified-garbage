module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.X86.Scrub
import VerifiedGarbage.Impl.Rc2.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc2.X86.Lit
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit
import VerifiedGarbage.Proof.Rc2.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC2 on x86 -/

namespace VG.Artifacts.Rc2.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Rc2.cbcInitApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Rc2.X86.Fn.cbcInitSsse3
    verified := Proof.Rc2.X86.Scrub.cbcInitSsse3_scrubbed },
  Spec.Rc2.cbcInitApi.artifact X86.target {
    code := Impl.Rc2.X86.Fn.cbcInit
    verified := Proof.Rc2.X86.Scrub.cbcInit_scrubbed },
  Spec.Rc2.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Rc2.X86.Fn.cbcEncryptChained
    verified := Proof.Rc2.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Rc2.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Rc2.X86.Fn.cbcDecryptChained
    verified := Proof.Rc2.X86.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Rc2.X86
