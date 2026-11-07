module

public import VerifiedGarbage.Proof.Camellia.X86.CtrVerified
public import VerifiedGarbage.Proof.Camellia.X86.CtrFinal
import VerifiedGarbage.Proof.Camellia.X86.CtrLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # Camellia-CTR artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.X86

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ctr
    stack := 2772
    verified := Proof.Camellia.X86.Ctr.ctr_framed },
  Spec.Camellia.ctrFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 60 5 8 Impl.Camellia.X86.ctrFinal
    stack := 2856
    verified := Proof.Camellia.X86.CtrFinal.ctrFinal_framed
    spSafe := Proof.Camellia.X86.CtrFinal.ctrFinal_framed_spSafe }]

end VG.Artifacts.CamelliaCtr.X86
