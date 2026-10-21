module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTMontOne
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontStride
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontData
meta import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontData
public import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract

/-! The compact RSA key-array view and its constants have public preparation traces. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

def MontKeyStart (p : MontMathData) (s : State) : Prop :=
  Workspace s p.base (8 * p.capacity) ∧ MontData p.base p.capacity p.words s.mem ∧
  (∃ k, p.words = Spec.Rsa.modulusWords k ∧ 64 ≤ k ∧ k ≤ 1024 ∧ Spec.Rsa.scratchWords k ≤ p.capacity) ∧
  InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 ∧ s.mem.readW (State.addr s.sp) 32 = p.base

private def MontBasePointer (p : MontMathData) (s : State) : Prop := s.gpr .r0 = p.base
private def MontKeyReady (p : MontMathData) (s : State) : Prop := KeyReady p.base p.capacity p.words s

private theorem keyHeader_taint : CandidateCert [.r0]
    (.block ((VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext.drop 1) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride)) :=
  ⟨_, by taint_decide⟩

private theorem keyArrays_taint : CandidateCert [.r7, .r8, .r9]
    VG.Impl.Ffdh.Arm.ParameterCandidate.montKeyArrays := ⟨_, by taint_decide⟩

private theorem keyHeader_ready (p : MontMathData) (s : State) (h : MontKeyStart p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext ++ VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride)) s
      (MontKeyReady p) := by
  obtain ⟨k, width, lower, upper, space⟩ := h.2.2.1
  rw [WP.block_append_iff]
  have data : MontData p.base p.capacity (Spec.Rsa.modulusWords k) s.mem := by rw [← width]; exact h.2.1
  refine WP.mono (keyContext_ready s h.1 data lower upper space h.2.2.2.1 h.2.2.2.2) ?_
  rintro u ⟨ready, ptr, _, rest⟩
  refine WP.mono (keyStride_words (h.1.congr rest.wr) ready ptr) ?_
  rintro t ⟨_, restT⟩
  rw [← width] at ready
  exact ready.rest restT (by simp) (by simp) (by simp)

theorem montKeySetup_ct : RelCT isa (Two MontKeyStart) VG.Impl.Ffdh.Arm.ParameterCandidate.montKeySetup (fun _ _ => True) := by
  have load : RelCT isa (Two MontKeyStart) (.block [.ldrSp .r0 0]) (Two MontBasePointer) :=
    two_post ((loadStack_ct .r0 0).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine wp_loadStack (a := State.addr s.sp) (by decide) (by simp only [BitVec.add_zero]) h.2.2.2.1 fun t loaded => WP.block_nil ?_
      exact loaded.gpr.trans h.2.2.2.2)
  obtain ⟨headerHint, headerChecked⟩ := keyHeader_taint
  have tail : RelCT isa (Two MontBasePointer)
      (.block ((VG.Impl.Ffdh.Arm.ParameterCandidate.keyContext.drop 1) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride))
      (fun _ _ => True) := by
    refine two_taint [.r0] ?_ headerChecked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.trans b.symm
  have header := two_post (RelCT.block_append (load.seq tail)) keyHeader_ready
  obtain ⟨arrayHint, arrayChecked⟩ := keyArrays_taint
  have arrays : RelCT isa (Two MontKeyReady) VG.Impl.Ffdh.Arm.ParameterCandidate.montKeyArrays (fun _ _ => True) := by
    refine two_taint [.r7, .r8, .r9] ?_ arrayChecked
    intro p s t a b r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact a.r7.trans b.r7.symm
    · exact a.r8.trans b.r8.symm
    · exact a.r9.trans b.r9.symm
  exact header.seq arrays

end VG.Proof.Ffdh.Arm.ParameterCandidate
