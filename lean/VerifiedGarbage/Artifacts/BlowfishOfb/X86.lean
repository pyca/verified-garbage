module

public import VerifiedGarbage.Proof.Blowfish.X86.FbVerified
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.X86

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.ofb
    stack := 112
    verified := Proof.Blowfish.X86.Fb.ofb_framed }]

end VG.Artifacts.BlowfishOfb.X86
