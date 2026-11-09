module

public import VerifiedGarbage.Proof.Sm4.X86_64.FbVerified
public import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalLit

/-! # SM4-OFB artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ofb
    stack := 3216
    verified := Proof.Sm4.X86_64.ofb_framed },
  Spec.Sm4.ofbFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ofbFinal
    stack := 3216
    verified := Proof.Sm4.X86_64.ofbFinal_framed }]

end VG.Artifacts.Sm4Ofb.X86_64
