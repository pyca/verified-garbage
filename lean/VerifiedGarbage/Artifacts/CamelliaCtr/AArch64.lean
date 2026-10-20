module

public import VerifiedGarbage.Proof.Camellia.AArch64.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CTR artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact AArch64.target {
    notes := ["Baseline AArch64: eight counter blocks at a time, encrypted bitsliced in general-purpose registers, the S-boxes as Boolean circuits, with no table lookups; the table of bitsliced subkeys is built once per call, by a call of `vg_camellia_prepare_keys`, and each batch is a call of `vg_camellia_crypt_prepared`. The mode is the generic CTR of `Impl/Modes/AArch64/`, over Camellia's ECB core."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.ctr
    stack := 3344
    verified := Proof.Camellia.AArch64.ctr_framed }]

end VG.Artifacts.CamelliaCtr.AArch64
