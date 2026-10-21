module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.OnPass
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The successful-witness countdown follows the public round policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure PassData where
  passed : Nat
  checks : Nat

structure PassStart (p : PassData) (s : State) : Prop where
  stack : Workspace s s.sp 72
  more : p.passed < p.checks
  bound : p.checks ≤ 128
  passed : s.mem.readW (State.addr (s.sp + 56#32)) 32 = BitVec.ofNat 32 p.passed
  checks : s.mem.readW (State.addr (s.sp + 52#32)) 32 = BitVec.ofNat 32 p.checks

private def PassHead (p : PassData) (s : State) : Prop := s.z = decide (p.passed + 1 = p.checks)

theorem onPass_ct : RelCT isa (Two PassStart) VG.Impl.Ffdh.Arm.ParameterCandidate.onPass (fun _ _ => True) := by
  have head : RelCT isa (Two PassStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.onPassHead) (Two PassHead) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial))
      (fun _ _ h => WP.mono (passHead_ok h.stack h.more h.bound h.passed h.checks) (fun _ post => post.1.2.1))
  have choice : RelCT isa (Two PassHead)
      (.ite .eq (.block [.mov .r3 (.imm 1)]) (.block [.mov .r3 (.imm 4)])) (fun s t => s.sp = t.sp) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left, right]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ h => h)
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ h => h)
  have finish : RelCT isa (fun s t => s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.onPassFinish) (fun s t => s.sp = t.sp) :=
    RelCT.block_append ((save_ct .r1 56).seq (stackOnly_ct [.cmp .r3 (.imm 4)] rfl))
  exact head.seq (choice.seq (finish.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
