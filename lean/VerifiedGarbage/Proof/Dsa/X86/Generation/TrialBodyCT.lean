module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialLoopCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialEntry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialLoopCT

/-! # Trial initialization and return expose only public candidate decisions -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def TrialEntryAt (len entries : Nat) (p : TrialPublic) (s : State) : Prop :=
  TrialInputs s p.base p.input p.table len entries ∧ trialValue s p.input len = p.value ∧
    s.gpr .esi = p.input ∧ s.gpr .edi = p.table

theorem trialEntry_ct (len entries : Nat) :
    RelCT isa (Two (TrialEntryAt len entries)) (.block trialCheckEntry)
      (Two fun (p : TrialPublic) s => 0 < entries ∧ TrialAt len entries {p with index := 0} s) := by
  refine two_piece [.esp, .esi, .edi] ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact BitVec.eq_of_toNat_eq (hs.1.frame.espNat.trans ht.1.frame.espNat.symm)
    · exact hs.2.2.1.trans ht.2.2.1.symm
    · exact hs.2.2.2.trans ht.2.2.2.symm
  · intro p s R
    refine WP.mono (trialCheckEntry_ok (TrialContext.refl R.1.frame) R.2.2.1 R.2.2.2)
      fun t ⟨C, src, tab, idx, status⟩ => ?_
    exact ⟨R.1.entriesPos, s, R.1, R.2.1, C, src, tab, idx, status, by intro j hj; change j < 0 at hj; omega⟩

theorem trialCheckBody_ct (len entries : Nat) :
    RelCT isa (Two (TrialEntryAt len entries)) (trialCheckBody len entries) (fun _ _ => True) := by
  unfold trialCheckBody
  refine RelCT.seq (trialEntry_ct len entries) (RelCT.seq
    (two_map (fun p : TrialPublic => {p with index := 0}) (fun _ _ h => h) (trialLoop_ct len entries)) ?_)
  refine two_taint [.esp] ?_ (by taint_decide)
  rintro p s t ⟨a, _, _, Ca, _⟩ ⟨b, _, _, Cb, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (Ca.frame.espNat.trans Cb.frame.espNat.symm)
end VG.Proof.Dsa.X86.Generation
