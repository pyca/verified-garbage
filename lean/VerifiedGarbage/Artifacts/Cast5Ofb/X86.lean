module

public import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
public import VerifiedGarbage.Proof.Cast5.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit

/-! # CAST5-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.X86

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.ofb
    stack := 336
    verified := Proof.Cast5.ofb_keyed Proof.Cast5.X86.ModeFns.ofb_framed },
  Spec.Cast5.ofbFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.ofbFinal
    stack := 336
    verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.X86.FbFinal.ofbFinal_framed }]

end VG.Artifacts.Cast5Ofb.X86
