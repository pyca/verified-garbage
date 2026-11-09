module

public import VerifiedGarbage.Proof.Blowfish.X86_64.FbVerified
public import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Blowfish-OFB artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.ofb
    stack := 96
    verified := Proof.Blowfish.X86_64.ofb_framed },
  Spec.Blowfish.ofbFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.ofbFinal
    stack := 96
    verified := Proof.Blowfish.X86_64.ofbFinal_framed }]

end VG.Artifacts.BlowfishOfb.X86_64
