module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTMontInput
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTMontOne
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTMontKey
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Complete native Montgomery preparation reuses RSA's constant-time math and array view. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_map)

def montMath (p : MontInputData) : MontMathData := ⟨p.base, p.capacity, Spec.Rsa.modulusWords p.k⟩

def MontFullStart (p : MontInputData) (s : State) : Prop := MontStart p s ∧ Spec.Rsa.scratchWords p.k ≤ p.capacity

private def MontHeaderStart (p : MontInputData) (s : State) : Prop := PreparedInput p s ∧ Spec.Rsa.scratchWords p.k ≤ p.capacity

private def MontLayoutState (p : MontInputData) (s : State) : Prop := MontR2 (montMath p) s ∧
  64 ≤ p.k ∧ p.k ≤ 1024 ∧ Spec.Rsa.scratchWords p.k ≤ p.capacity

private def MontKeyState (p : MontInputData) (s : State) : Prop := MontKeyStart (montMath p) s

theorem montPrep_ct : RelCT isa (Two MontFullStart) VG.Impl.Ffdh.Arm.ParameterCandidate.montPrep (fun _ _ => True) := by
  have head : RelCT isa (Two MontFullStart) (.block [.ldrSp .r0 0, .ldrSp .r6 12]) (Two MontHeaderStart) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h =>
      WP.mono (prepareHeader_ok p s h.1) (fun _ result => ⟨result, h.2⟩))
  have prepareTrace : RelCT isa (Two MontHeaderStart) VG.Impl.Ffdh.Arm.prepare (fun _ _ => True) := by
    intro s t trS trT u v h runS runT
    obtain ⟨p, left, right, sp⟩ := h
    have countFits : 128 * Spec.Rsa.modulusWords p.k < 2 ^ 32 := by
      have bound := left.1.maxLength
      dsimp only [Spec.Rsa.modulusWords]
      omega
    exact prepare_ct countFits _ _ _ _ _ _ ⟨left.1, right.1, sp⟩ runS runT
  have prepare : RelCT isa (Two MontHeaderStart) VG.Impl.Ffdh.Arm.prepare (Two MontLayoutState) :=
    two_post prepareTrace (fun p s h => by
      refine WP.mono (prepare_ok s h.1) ?_
      rintro t ⟨ready, number, r2, _, _⟩
      refine ⟨⟨ready, ?_⟩, h.1.minLength, h.1.maxLength, h.2⟩
      change numAt t.mem (State.addr p.base) (Spec.Rsa.modulusWords p.k) 4 < numAt t.mem (State.addr p.base) (Spec.Rsa.modulusWords p.k) 0
      rw [r2, number]
      exact Nat.mod_lt _ (by have := h.1.large; omega))
  have oneTrace : RelCT isa (Two MontLayoutState)
      (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.montOp 1 1 4)) (fun _ _ => True) :=
    two_map montMath (fun _ _ h => h.1) montOne_ct
  have one : RelCT isa (Two MontLayoutState)
      (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.montOp 1 1 4)) (Two MontKeyState) :=
    two_post oneTrace (fun p s h => by
      refine WP.mono (montOne_ready (montMath p) s h.1) ?_
      intro t ready
      exact ⟨ready.workspace, MontData.of_ready ready, ⟨p.k, rfl, h.2⟩, ready.stackRead, ready.saved⟩)
  have key := two_map montMath (fun _ _ h => h) montKeySetup_ct
  exact head.seq (prepare.seq (one.seq (key.seq (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
