module

public import VerifiedGarbage.Proof.Ffdh.VettedGroupFacts

/-! Compatibility names for the AArch64 policy's shared, ISA-independent facts. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.PolicyFacts
export VG.Proof.Ffdh.VettedGroupFacts (group_bounds group_aligned width_unique width_unique_word domain_parts domain_encoding domainOf_injective group_take_two group_take_three domainOf_two domainOf_three NumericMatch numericRecognize group_parameters group_match_iff numericRecognize_spec recognize_spec)
end VG.Proof.Ffdh.AArch64.Cached.PolicyFacts
