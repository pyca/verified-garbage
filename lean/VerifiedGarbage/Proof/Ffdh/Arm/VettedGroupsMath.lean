module

public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.VettedGroupFacts

/-! Canonical byte comparisons recognize exactly the reviewed group policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups

export VG.Proof.Ffdh.VettedGroupFacts
  (group_bounds group_aligned width_unique width_unique_word domain_parts domain_encoding
   domainOf_injective group_take_two group_take_three domainOf_two domainOf_three
   NumericMatch numericRecognize group_parameters group_match_iff numericRecognize_spec)

theorem recognize_spec {k : Nat} {dom : List VG.Byte} (positive : 0 < k)
    (size : dom.length = 2 * k ∨ dom.length = 3 * k)
    (normalized : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ VG.Spec.Rsa.os2ip (dom.take k)) :
    VG.Impl.Ffdh.Arm.VettedGroups.recognize VG.Impl.Ffdh.Arm.VettedGroups.groups k dom =
      (VG.Spec.Ffdh.vettedExponentBits (VG.Spec.Ffdh.domainOf k dom)).getD 0 := by
  exact VG.Proof.Ffdh.VettedGroupFacts.recognize_spec positive size normalized

end VG.Proof.Ffdh.Arm.VettedGroups
