module

public import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.FbLit

/-! # Triple DES-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.X86

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofb
    stack := 984
    verified := Proof.TripleDes.X86.Fb.ofb_framed }]

end VG.Artifacts.TripleDesOfb.X86
