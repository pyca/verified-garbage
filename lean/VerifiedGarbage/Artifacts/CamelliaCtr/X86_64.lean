module

public import VerifiedGarbage.Proof.Camellia.X86_64.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CTR artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact X86_64.target {
    notes := ["Baseline x86-64: eight counter blocks at a time, encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups; the table of bitsliced subkeys is built once per call, inline, and each batch is a call of `vg_camellia_crypt_prepared`. The mode is the generic CTR of `Impl/Modes/X86_64/`, over Camellia's ECB core."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.ctr
    stack := 3288
    verified := Proof.Camellia.X86_64.ctr_framed }]

end VG.Artifacts.CamelliaCtr.X86_64
