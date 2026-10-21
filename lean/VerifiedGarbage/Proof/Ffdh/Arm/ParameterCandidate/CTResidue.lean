module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResiduePrime
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResidue2
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Residue
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete generator dispatch and congruence filtering depend only on public inputs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_map two_ite)

def ResiduePublic (p : TrialData × Nat) (s : State) : Prop :=
  TrialBuffers p.1 s ∧ (p.2 = 2 ∨ p.2 = 5) ∧
    s.mem.readW (State.addr (s.sp + 28#32)) 32 = BitVec.ofNat 32 p.2

private def ResidueReady (p : TrialData × Nat) (s : State) : Prop :=
  ResiduePublic p s ∧ s.z = decide (p.2 = 2)

private def residueTrial (p : TrialData × Nat) (prime : BitVec 32) : TrialData := { p.1 with prime := prime }

theorem residue_ct : RelCT isa (Two ResiduePublic) VG.Impl.Ffdh.Arm.ParameterCandidate.residue (fun _ _ => True) := by
  have head : RelCT isa (Two ResiduePublic) (.block [.ldrSp .r1 28, .cmp .r1 (.imm 2)]) (Two ResidueReady) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine WP.mono (residueHead_ok h.1.1 (by rcases h.2.1 with eq | eq <;> omega) h.2.2) ?_
      rintro t ⟨⟨flag, memory⟩, rest⟩
      exact ⟨⟨⟨h.1.1.after_memory memory rest, by rw [memory]; exact h.1.2⟩, h.2.1,
        by rw [memory, rest.sp]; exact h.2.2⟩, flag⟩)
  have branch : RelCT isa (Two ResidueReady)
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.residue2 VG.Impl.Ffdh.Arm.ParameterCandidate.residue5) (fun _ _ => True) := by
    refine two_ite (fun p s t a b => by change some s.z = some t.z; rw [a.2, b.2]) ?_ ?_
    · refine two_map (fun p => residueTrial p 3#32) ?_ residue2_ct
      intro p s h
      exact ⟨h.1.1.1, rfl⟩
    · have five := residuePrime_ct 5 [2, 3, 7, 8] (by decide) residue5Equals_taint
      refine two_map (fun p => residueTrial p 5#32) ?_ five
      intro p s h
      exact ⟨h.1.1.1, rfl⟩
  exact head.seq branch

end VG.Proof.Ffdh.Arm.ParameterCandidate
