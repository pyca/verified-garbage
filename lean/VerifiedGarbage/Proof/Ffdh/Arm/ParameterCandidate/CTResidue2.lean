module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResiduePrime
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResidueLow
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResidueLow
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Generator-two filtering branches only on its public low candidate octet. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_map two_ite)

def Residue2Start (p : TrialData) (s : State) : Prop := TrialBuffers p s ∧ p.prime = 3#32

private def Residue2Low (p : TrialData) (s : State) : Prop := Residue2Start p s ∧
  s.z = decide ((p.values[0]?.getD 0).toNat % 8 = 3)

theorem residue2_ct : RelCT isa (Two Residue2Start) VG.Impl.Ffdh.Arm.ParameterCandidate.residue2 (fun _ _ => True) := by
  have lowTrace : RelCT isa (Two Residue2Start) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow)
      (fun _ _ => True) :=
    two_map (fun p : TrialData => (p.dst, p.n)) (fun _ _ h => h.1.1) residueLow_ct
  have low : RelCT isa (Two Residue2Start) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow) (Two Residue2Low) :=
    two_post lowTrace (fun p s h => by
      refine WP.mono (residueLow_ok s p.dst p.n (h.1.1.frame.read (by decide)) (h.1.1.frame.read (by decide))
        h.1.1.out h.1.1.width (h.1.1.readable.low h.1.1.positive)) ?_
      rintro t ⟨⟨flag, memory⟩, rest⟩
      have last : s.mem (State.addr (p.dst + BitVec.ofNat 32 p.n - 1)) = p.values[0]?.getD 0 := h.1.2 0 h.1.1.positive
      rw [last] at flag
      exact ⟨⟨⟨h.1.1.after_memory memory rest, by rw [memory]; exact h.1.2⟩, h.2⟩, flag⟩)
  have branch : RelCT isa (Two Residue2Low)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.residuePrime 3 [2, 5]) (.block [])) (fun _ _ => True) := by
    refine two_ite (fun p s t a b => by change some s.z = some t.z; rw [a.2, b.2]) ?_ ?_
    · exact (residuePrime_ct 3 [2, 5] (by decide) residue2Equals_taint).mono
        (fun _ _ ⟨p, a, b, sp⟩ => ⟨p, a.1.1, b.1.1, sp⟩) (fun _ _ h => h)
    · exact RelCT.block_nil (fun _ _ _ => trivial)
  exact low.seq branch

end VG.Proof.Ffdh.Arm.ParameterCandidate
