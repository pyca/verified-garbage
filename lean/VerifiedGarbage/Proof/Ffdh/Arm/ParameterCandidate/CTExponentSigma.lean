module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCountLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ExponentSigma
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase

/-! The compact-round shift depends only on the public decomposition count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure SigmaStart (count : Nat) (s : State) : Prop where
  stack : Workspace s s.sp 72
  saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count

private def SigmaHead (count : Nat) (s : State) : Prop := s.z = decide (count % 4 = 0)

private theorem sigmaHead_ct : RelCT isa (Two SigmaStart)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigmaHead) (Two SigmaHead) := by
  refine two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) ?_
  intro count s h
  exact WP.mono (sigmaHead_ok h.stack h.saved) (fun _ post => post.1.2.1)

theorem exponentSigma_ct : RelCT isa (Two SigmaStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma (fun s t => s.sp = t.sp) := by
  have choice : RelCT isa (Two SigmaHead)
      (.ite .eq (.block [.mov .r1 (.imm 4)]) (.block [])) (fun s t => s.sp = t.sp) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left, right]
    · exact (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ h => h)
    · exact RelCT.block_nil (fun _ _ ⟨_, _, _, sp⟩ => sp)
  exact sigmaHead_ct.seq (choice.seq ((save_ct .r1 64).seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
