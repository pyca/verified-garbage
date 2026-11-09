module

public import VerifiedGarbage.Proof.Camellia.X86.FbVerified
import VerifiedGarbage.Proof.Camellia.X86.FbLit
public import VerifiedGarbage.Proof.Camellia.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.FbFinalLit

/-! # Camellia-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.X86

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ofb
    stack := 2772
    verified := Proof.Camellia.X86.Fb.ofb_framed },
  Spec.Camellia.ofbFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ofbFinal
    stack := 2772
    verified := Proof.Camellia.X86.FbFinal.ofbFinal_framed }]

end VG.Artifacts.CamelliaOfb.X86
