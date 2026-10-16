module

public import VerifiedGarbage.Proof.Camellia.X86.CtrVerified
import VerifiedGarbage.Proof.Camellia.X86.CtrLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CTR artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.X86

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact X86.target {
    notes := ["Baseline IA-32: the generic CTR mode over Camellia’s bitsliced encryption core, one counter block at a time. The other seven lanes are unused; bitsliced subkeys are built once per call. The full 128-bit big-endian counter increment is verified, and working space is zeroed on return."]
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.ctr
    stack := 2756
    verified := Proof.Camellia.X86.Ctr.ctr_framed }]

end VG.Artifacts.CamelliaCtr.X86
