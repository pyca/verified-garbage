module

public import VerifiedGarbage.Proof.Sm4.X86.FbVerified
public import VerifiedGarbage.Proof.Sm4.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sm4.X86.FbLit
import VerifiedGarbage.Proof.Sm4.X86.FbFinalLit

/-! # SM4-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.X86

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ofb
    stack := 1516
    verified := Proof.Sm4.X86.Fb.ofb_framed },
  Spec.Sm4.ofbFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ofbFinal
    stack := 1516
    verified := Proof.Sm4.X86.FbFinal.ofbFinal_framed }]

end VG.Artifacts.Sm4Ofb.X86
