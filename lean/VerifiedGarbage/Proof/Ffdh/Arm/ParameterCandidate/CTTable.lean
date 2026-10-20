module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TablePointer
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The native RSA sieve table is written at the same public scratch offsets in both runs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

def TableStart (p : CandidateParams × Nat) (s : State) : Prop := CandidateContext p.1 p.2 s
private def TablePointer (p : CandidateParams × Nat) (s : State) : Prop :=
  s.gpr .r11 = p.1.base + BitVec.ofNat 32 (Spec.Rsa.Mont.arrAt p.1.words 34)

theorem tableWrite_ct : RelCT isa (Two TableStart)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite) (fun _ _ => True) := by
  have pointer : RelCT isa (Two TableStart) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tablePointer) (Two TablePointer) :=
    two_post ((stackOnly_ct _ (by decide)).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine WP.mono (tablePointer_ok s p.1.base p.1.length p.1.length_bounds.2
        (by simpa only [BitVec.add_zero] using h.saved.read (d := 0) (by decide)) (h.saved.read (by decide))
        (by simpa only [BitVec.add_zero, candidateValues] using h.saved.saved 0 (by decide)) (h.saved.saved 12 (by decide))) ?_
      rintro t ⟨⟨ptr, _⟩, _⟩
      exact ptr)
  obtain ⟨hint, checked⟩ := tableWrites_taint
  have writes : RelCT isa (Two TablePointer) (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrites 53))
      (fun _ _ => True) := by
    refine two_taint [.r11] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.trans b.symm
  exact RelCT.block_append (pointer.seq writes)

end VG.Proof.Ffdh.Arm.ParameterCandidate
