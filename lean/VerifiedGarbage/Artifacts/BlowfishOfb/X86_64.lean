module

public import VerifiedGarbage.Proof.Blowfish.X86_64.FbVerified
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-OFB artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.ofb
    stack := 96
    verified := Proof.Blowfish.X86_64.ofb_framed }]

end VG.Artifacts.BlowfishOfb.X86_64
