module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsPolicy
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsCT
import VerifiedGarbage.Proof.Ffdh.Arm.VettedCapPolicy
import VerifiedGarbage.Proof.Ffdh.Arm.VettedLayoutStandard

/-! # Exact-domain recognition supplies the reviewed public cap -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedBound
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

def cap (p : Inputs) : Nat :=
  (Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom)).getD 0

def code : Prog isa :=
  VG.Impl.Ffdh.Arm.VettedCap.bound VG.Impl.Ffdh.Arm.VettedGroups.code

theorem recognize_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (environment : VettedGroups.environment.holds p s)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa VG.Impl.Ffdh.Arm.VettedGroups.code s fun t => Context p slots t ∧
      t.gpr .r11 = BitVec.ofNat 32 (cap p) ∧ t.mem = s.mem ∧ Rest roundClobbers s t :=
  vettedGroups_ok s h h24 h28 h32 environment.1 normalized

theorem layoutLaw : VettedCap.LayoutLaw cap ScalarLayout.vetted := by
  constructor
  · intro p normalized odd zero
    cases recognized : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom) with
    | none =>
      have width := p.width.1
      have low : 2 ^ 64 ≤ 2 ^ (64 * (p.w - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      have large : 1 < p.P := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide : 1 < (2 : Nat) ^ 64) low) normalized
      exact vetted_layout_unrecognized recognized large odd
    | some bits =>
      have nonzero : BitVec.ofNat 32 bits ≠ 0 := by
        rcases vetted_caps recognized with rfl | rfl | rfl | rfl | rfl <;> decide
      exact False.elim (nonzero (by simpa only [cap, recognized, Option.getD_some] using zero))
  · intro p _normalized _odd nonzero old
    cases recognized : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom) with
    | none => exact False.elim (nonzero (by simp only [cap, recognized, Option.getD_none]; rfl))
    | some bits =>
      simpa only [cap, recognized, Option.getD_some] using vetted_cap_layout recognized old


theorem recognitionLaw : VettedCap.RecognitionLaw VettedGroups.environment cap
    VG.Impl.Ffdh.Arm.VettedGroups.code where
  correct := by
    intro s p slots h environment normalized h24 h28 h32
    exact recognize_ok s h environment normalized h24 h28 h32
  ct := by
    intro p slots _normalized h24 h28 h32
    exact (VettedGroups.code_ct h24 h28 h32).mono
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩) (fun _ _ _ => trivial)

theorem law : SampleBoundLaw VettedGroups.environment ScalarLayout.vetted code :=
  VettedCap.boundLaw recognitionLaw layoutLaw


end VG.Proof.Ffdh.Arm.VettedBound
