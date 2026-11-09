module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalLit

/-! # Triple DES-OFB artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.X86_64

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.ofb
    stack := 984
    verified := Proof.TripleDes.X86_64.ofb_framed },
  Spec.TripleDes.ofbFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.ofbFinal
    stack := 984
    verified := Proof.TripleDes.X86_64.ofbFinal_framed }]

end VG.Artifacts.TripleDesOfb.X86_64
