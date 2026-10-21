module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! The parity prefilter reads one public candidate address. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

private def LowPointers (p : BitVec 32 × Nat) (s : State) : Prop :=
  s.gpr .r4 = p.1 ∧ s.gpr .r5 = BitVec.ofNat 32 p.2

private theorem qOdd_tail_taint : ∃ hint, (VG.Taint.check taint (Taint.ofRegs [.r4, .r5])
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd.drop 2)) hint).isSome = true := ⟨_, by taint_decide⟩

theorem qOdd_ct : RelCT isa (Two fun (p : BitVec 32 × Nat) s => ReadContext p.1 p.2 s)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd) (fun _ _ => True) := by
  have head : RelCT isa (Two fun (p : BitVec 32 × Nat) s => ReadContext p.1 p.2 s)
      (.block [.ldrSp .r4 4, .ldrSp .r5 12]) (Two LowPointers) :=
    two_post ((stackLoads_ct [(.r4, 4), (.r5, 12)]).mono
      (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      have out : s.mem.readW (State.addr (s.sp + 4#32)) 32 = p.1 := h.out
      have width : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 p.2 := h.width
      ffrun [LowPointers, h.frame.read (d := 4) (by decide), h.frame.read (d := 12) (by decide), out, width])
  obtain ⟨hint, checked⟩ := qOdd_tail_taint
  have tail : RelCT isa (Two LowPointers) (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd.drop 2))
      (fun _ _ => True) := by
    refine two_taint [.r4, .r5] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact a.1.trans b.1.symm
    · exact a.2.trans b.2.symm
  exact RelCT.block_append (head.seq tail)

end VG.Proof.Ffdh.Arm.ParameterCandidate
