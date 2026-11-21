module

public import VerifiedGarbage.Proof.Rc2.X86.Scrub
public import VerifiedGarbage.Impl.Rc2.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Rc2.X86.Lit
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit

/-! # RC2 on x86 -/

@[expose] public section

namespace VG.Artifacts.Rc2.X86

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact X86.target {
    code := Impl.Rc2.X86.Fn.cbcInit
    verified := Proof.Rc2.X86.Scrub.cbcInit_scrubbed },
  Spec.Rc2.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Rc2.X86.Fn.cbcEncryptChained
    verified := Proof.Rc2.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Rc2.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Rc2.X86.Fn.cbcDecryptChained
    verified := Proof.Rc2.X86.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.Rc2.X86
