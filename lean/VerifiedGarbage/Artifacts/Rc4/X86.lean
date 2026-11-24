module

public import VerifiedGarbage.Proof.Rc4.X86.Scrub
public import VerifiedGarbage.Impl.Rc4.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Rc4.X86.Lit

/-! # RC4 on x86 -/

@[expose] public section

namespace VG.Artifacts.Rc4.X86

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact X86.target {
    code := Impl.Rc4.X86.Fn.init
    verified := Proof.Rc4.X86.Scrub.init_scrubbed },
  Spec.Rc4.applyApi.artifact X86.target {
    code := Impl.Rc4.X86.Fn.apply
    verified := Proof.Rc4.X86.Scrub.apply_scrubbed }]

end VG.Artifacts.Rc4.X86
