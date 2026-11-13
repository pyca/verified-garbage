module

public import VerifiedGarbage.Proof.Rc4.X86_64.Verified
public import VerifiedGarbage.Proof.Rc4.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Rc4.X86_64.Lit

/-! # RC4 on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Rc4.X86_64

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact X86_64.target Proof.Rc4.X86_64.Scrub.initReg,
  Spec.Rc4.applyApi.artifact X86_64.target Proof.Rc4.X86_64.Scrub.applyReg]

end VG.Artifacts.Rc4.X86_64
