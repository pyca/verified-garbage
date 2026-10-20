module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTMontPrepare
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentSetup

/-! Complete Montgomery and compact-round preparation for a public candidate. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure PreparationData where
  input : MontInputData
  modulus : Nat

structure PreparationStart (p : PreparationData) (s : State) : Prop where
  input : MontFullStart p.input s
  stack : Workspace s s.sp 72
  separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.input.base, 8 * p.input.capacity⟩
  modulus : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.input.src) p.input.k) = p.modulus

private theorem montDecompose_ok (p : PreparationData) (s : State) (h : PreparationStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep s (DecomposeStart ⟨montMath p.input, p.modulus⟩) := by
  refine WP.mono (montPrep_ok h.input.1 h.input.2) ?_
  rintro t ⟨ready, data, full, _, _, _, _, _, _, rest⟩
  rw [h.modulus] at full
  exact ⟨h.input.1.workspace.congr rest.wr, ready, data,
    by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, full,
    h.modulus ▸ h.input.1.large, h.modulus ▸ h.input.1.odd⟩

theorem phasePrepared_ct : RelCT isa (Two PreparationStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared (fun _ _ => True) := by
  have trace : RelCT isa (Two PreparationStart) VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep (fun _ _ => True) :=
    two_map PreparationData.input (fun _ _ h => h.input) montPrep_ct
  exact (two_post trace montDecompose_ok).seq
    (expSetup_ct.mono
      (fun _ _ ⟨p, left, right, sp⟩ => ⟨⟨montMath p.input, p.modulus⟩, left, right, sp⟩)
      (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
