module

public import VerifiedGarbage.Proof.Rc4.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Rc4.PPC64LE.Lit

/-! # RC4 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rc4.PPC64LE

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact PPC64LE.target Proof.Rc4.PPC64LE.Scrub.initReg,
  Spec.Rc4.applyApi.artifact PPC64LE.target Proof.Rc4.PPC64LE.Scrub.applyReg]

end VG.Artifacts.Rc4.PPC64LE
