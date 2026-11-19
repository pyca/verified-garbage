module

public import VerifiedGarbage.Proof.Md5.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Md5.X86.Lit

/-! # MD5 (RFC 1321) on x86 -/

@[expose] public section

namespace VG.Artifacts.Md5.X86

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact X86.target Proof.Md5.X86.Scrub.initReg,
  Spec.Md5.updateApi.artifact X86.target Proof.Md5.X86.Scrub.updateReg,
  Spec.Md5.finalizeApi.artifact X86.target Proof.Md5.X86.Scrub.finalizeReg]

end VG.Artifacts.Md5.X86
