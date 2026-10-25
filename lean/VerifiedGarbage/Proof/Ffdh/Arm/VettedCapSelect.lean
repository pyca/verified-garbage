module

public import VerifiedGarbage.Impl.Ffdh.Arm.VettedCap
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! The public-cap decision tree changes only the width and mask registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedCap
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedCap
open VG.Proof.X25519.Arm (Rest)

theorem test_ok (s : State) (c : Choice) :
    WP isa (.block (test c)) s fun t =>
      (t.z = (s.gpr .r11 - c.bits.setWidth 32 == 0) ∧ t.mem = s.mem) ∧ Rest [.r12] s t := by
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold test
  ffrun []

theorem selected_ok (s : State) (c : Choice) :
    WP isa (.block (selected c)) s fun t =>
      (t.gpr .r6 = c.width.setWidth 32 ∧ t.gpr .r3 = c.mask.setWidth 32 ∧ t.mem = s.mem) ∧
      Rest [.r3, .r6] s t := by
  refine withRest_all [.r3, .r6] ?_ (by rfl) (by rfl)
  unfold selected
  ffrun []

theorem choose_ok (cs : List Choice) (s : State) :
    WP isa (choose cs) s fun t =>
      (t.gpr .r6, t.gpr .r3) = result cs (s.gpr .r11) (s.gpr .r6, s.gpr .r3) ∧
      t.mem = s.mem ∧ Rest [.r3, .r6, .r12] s t := by
  induction cs generalizing s with
  | nil =>
    exact WP.block_nil ⟨rfl, rfl, Rest.refl _ _⟩
  | cons c cs ih =>
    rw [choose, WP.seq_iff]
    refine WP.mono (test_ok s c) ?_
    rintro u ⟨⟨flag, memU⟩, restU⟩
    have kept11 := restU.gpr .r11 (by simp)
    have kept6 := restU.gpr .r6 (by simp)
    have kept3 := restU.gpr .r3 (by simp)
    cases eqn : (s.gpr .r11 - c.bits.setWidth 32 == 0) with
    | true =>
      refine WP.ite true (by change some u.z = some true; rw [flag, eqn]) ?_ (by simp)
      intro _
      refine WP.mono (selected_ok u c) ?_
      rintro t ⟨⟨width, mask, memT⟩, restT⟩
      exact ⟨by simp only [result, eqn, ite_true, width, mask], memT.trans memU,
        (restU.mono (by simp)).trans (restT.mono (by simp))⟩
    | false =>
      refine WP.ite false (by change some u.z = some false; rw [flag, eqn]) (by simp) ?_
      intro _
      refine WP.mono (ih u) ?_
      rintro t ⟨value, memT, restT⟩
      exact ⟨by
          simp only [result, eqn, Bool.false_eq_true, ite_false]
          simpa only [kept11, kept6, kept3] using value,
        memT.trans memU, (restU.mono (by simp)).trans restT⟩

end VG.Proof.Ffdh.Arm.VettedCap
