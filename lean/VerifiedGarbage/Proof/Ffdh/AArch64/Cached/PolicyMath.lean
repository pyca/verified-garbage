module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyBytes
public import VerifiedGarbage.Proof.Ffdh.VettedGroupFacts
/-! The AArch64 recognizer's data is exactly the existing reviewed policy table.
These are value-level facts; instruction correctness is proved separately. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyFacts.lean`, which only this module imported.
section

/-! Compatibility names for the AArch64 policy's shared, ISA-independent facts. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.PolicyFacts
export VG.Proof.Ffdh.VettedGroupFacts (group_bounds group_aligned width_unique width_unique_word domain_parts domain_encoding domainOf_injective group_take_two group_take_three domainOf_two domainOf_three NumericMatch numericRecognize group_parameters group_match_iff numericRecognize_spec recognize_spec)
end VG.Proof.Ffdh.AArch64.Cached.PolicyFacts
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.Policy
open VG VG.Impl.Ffdh.AArch64.Cached.Policy

theorem tableBytes_length : tableBytes.length=17744 :=PolicyFacts.tableBytes_length

theorem tableWords_length : tableWords.length=2218 :=PolicyFacts.tableWords_length

/-- A complete byte comparison implements the common exact-group policy. -/
theorem recognize_spec {k : Nat} {dom : List Byte} (positive : 0 < k)
 (size : dom.length = 2*k ∨ dom.length = 3*k)
 (normalized : 2^(64*((k+7)/8-1)) ≤ Spec.Rsa.os2ip (dom.take k)) :
 VG.Impl.Ffdh.AArch64.Cached.Policy.recognizeList groups k dom =
 (Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom)).getD 0 := by
 exact VG.Proof.Ffdh.AArch64.Cached.PolicyFacts.recognize_spec positive size normalized

end VG.Proof.Ffdh.AArch64.Cached.Policy
