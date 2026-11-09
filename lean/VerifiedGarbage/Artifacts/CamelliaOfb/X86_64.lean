module

public import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit

/-! # Camellia-OFB artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ofb
    stack := 3288
    verified := Proof.Camellia.X86_64.ofb_framed },
  Spec.Camellia.ofbFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ofbFinal
    stack := 3288
    verified := Proof.Camellia.X86_64.ofbFinal_framed }]

end VG.Artifacts.CamelliaOfb.X86_64
