module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! In-place q construction traverses precisely the public candidate width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

def HalveRead (p : BitVec 32 × Nat) (s : State) : Prop := ReadContext p.1 p.2 s
private def HalvePointers (p : BitVec 32 × Nat) (s : State) : Prop :=
  s.gpr .r0 = p.1 ∧ s.gpr .lr = BitVec.ofNat 32 p.2

theorem halveQ_ct : RelCT isa (Two HalveRead) VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ (fun _ _ => True) := by
  have head : RelCT isa (Two HalveRead) (.block [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)]) (Two HalvePointers) :=
    two_post (halveHead_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      have out := h.out
      have width := h.width
      change s.mem.readW (State.addr (s.sp + 4#32)) 32 = p.1 at out
      change s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 p.2 at width
      ffrun [HalvePointers, BitVec.add_zero, h.frame.read (d := 4) (by decide), h.frame.read (d := 12) (by decide), out, width])
  obtain ⟨hint, checked⟩ := halveLoop_taint
  have loop : RelCT isa (Two HalvePointers) (.loop (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfByte) .ne)
      (fun _ _ => True) := by
    refine two_taint [.r0, .lr] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact a.1.trans b.1.symm
    · exact a.2.trans b.2.symm
  have tail : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.dp .and .r1 .r1 (.imm 1), .cmp .r1 (.imm 0)]) (fun _ _ => True) :=
    (stackOnly_ct _ rfl).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  exact head.seq ((relCT_keep_sp loop (fun _ _ ⟨_, _, _, sp⟩ => sp)).seq
    (tail.seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
