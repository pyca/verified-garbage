module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResultContext
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ClearOutput
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Final output clearing and u64 consumption stores use only public buffer addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

structure ResultData where
  dst : BitVec 32
  usedPtr : BitVec 32
  n : Nat
  consumed : Nat

def ResultStart (p : ResultData) (s : State) : Prop := ResultContext p.dst p.usedPtr p.n p.consumed s

private def ResultPointer (p : ResultData) (s : State) : Prop := s.gpr .r2 = p.usedPtr
private def ClearPointers (p : ResultData) (s : State) : Prop := s.gpr .r0 = p.dst ∧ s.gpr .lr = BitVec.ofNat 32 p.n

theorem finish_ct (status : Nat) (bound : status ≤ 2) : RelCT isa (Two ResultStart)
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.finish status)) (fun _ _ => True) := by
  have head : RelCT isa (Two ResultStart) (.block [.ldrSp .r2 32]) (Two ResultPointer) :=
    two_post ((loadStack_ct .r2 32).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine wp_loadStack (a := State.addr (s.sp + 32#32)) (by decide) rfl (h.saved.read (by decide)) fun t loaded => WP.block_nil ?_
      exact loaded.gpr.trans (h.saved.saved 32 (by decide)))
  obtain ⟨hint, checked⟩ := finishTail_taint status bound
  have tail : RelCT isa (Two ResultPointer) (.block ((VG.Impl.Ffdh.Arm.ParameterCandidate.finish status).drop 1))
      (fun _ _ => True) := by
    refine two_taint [.r2] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.trans b.symm
  exact RelCT.block_append (head.seq tail)

theorem clearOutput_ct : RelCT isa (Two ResultStart) VG.Impl.Ffdh.Arm.ParameterCandidate.clearOutput (Two ResultStart) := by
  have head : RelCT isa (Two ResultStart) (.block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)]) (Two ClearPointers) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun _ s h =>
      WP.mono (clearHead_ok h) (fun _ ⟨⟨ptr, count, _, _⟩, _⟩ => ⟨ptr, count⟩))
  obtain ⟨hint, checked⟩ := clearOutputLoop_taint
  have loop : RelCT isa (Two ClearPointers) VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeros (fun _ _ => True) := by
    refine two_taint [.r0, .lr] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact a.1.trans b.1.symm
    · exact a.2.trans b.2.symm
  exact two_post (head.seq loop) (fun _ _ h => WP.mono (clearOutput_ok h) (fun _ ⟨context, _, _, _⟩ => context))

private theorem loadConsumed_ct : RelCT isa (Two ResultStart) (.block [.ldrSp .r3 40]) (Two ResultStart) :=
  two_post ((loadStack_ct .r3 40).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun _ s h => by
    refine wp_loadStack (a := State.addr (s.sp + 40#32)) (by decide) rfl (h.saved.read (by decide)) fun t loaded => WP.block_nil ?_
    exact h.after_memory loaded.mem (loaded.rest (by simp : Reg.r3 ∈ [Reg.r3])))

private theorem zeroConsumed_ct : RelCT isa (Two ResultStart) (.block [.mov .r3 (.imm 0)]) (Two ResultStart) :=
  two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun _ _ h => by
    refine wp_mov (op2_imm (by decide)) fun t moved => WP.block_nil ?_
    exact h.after_memory moved.mem (moved.rest (by simp : Reg.r3 ∈ [Reg.r3])))

theorem finAccepted_ct : RelCT isa (Two ResultStart) VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted (fun _ _ => True) :=
  RelCT.block_append (loadConsumed_ct.seq (finish_ct 1 (by decide)))

theorem finRejected_ct : RelCT isa (Two ResultStart) VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected (fun _ _ => True) :=
  clearOutput_ct.seq (RelCT.block_append (loadConsumed_ct.seq (finish_ct 2 (by decide))))

theorem finNone_ct : RelCT isa (Two ResultStart) VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (fun _ _ => True) :=
  clearOutput_ct.seq (RelCT.block_append (zeroConsumed_ct.seq (finish_ct 0 (by decide))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
