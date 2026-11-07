module

public import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
public import VerifiedGarbage.Proof.TripleDes.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.TripleDes.X86.FbLit
import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit

/-! # Triple DES-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.X86

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofb
    stack := 984
    verified := Proof.TripleDes.X86.Fb.ofb_framed },
  Spec.TripleDes.ofbFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofbFinal
    stack := 984
    verified := Proof.TripleDes.X86.FbFinal.ofbFinal_framed }]

end VG.Artifacts.TripleDesOfb.X86
