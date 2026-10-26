module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTKeyRegisters
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyOps
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTKeyRegisters
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import Mathlib.Data.Int.ModEq

/-! Copy the public modulus while retaining the bounded shift counter. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

private theorem copy27_taint : CandidateCert keyRegs (VG.Impl.Rsa.Arm.Keys.copy 27 0) := ⟨_, by taint_decide⟩

private theorem copy27_ok (p : ExponentCountData) (s : State) (h : ExponentCountState p s) :
    WP isa (VG.Impl.Rsa.Arm.Keys.copy 27 0) s (ExponentCountState p) := by
  refine WP.mono (keyCopy_ok h.workspace h.ready (o := 27) (a := 0) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨ready, keep, _, rest⟩
  have frame := key_keep_workspace h.workspace h.ready (by simp) keep
  have saved : t.mem.readW (State.addr (t.sp + 64#32)) 32 = BitVec.ofNat 32 p.count := by
    rw [rest.sp, frame.readW (r := ⟨State.addr (s.sp + 64#32), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact h.saved
    · intro r hr
      rw [List.mem_singleton] at hr
      subst r
      rw [VG.Arm.addr_add (by have := h.stack.nowrap; omega)]
      exact h.separate.sub_left (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))
  exact ⟨h.workspace.congr rest.wr, ready,
    (h.data.after_key_keep h.workspace h.ready (by simp) (by simp) keep).1,
    by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, h.positive, h.bound, saved⟩

theorem exponentCopy_ct : RelCT isa (Two ExponentCountState) (VG.Impl.Rsa.Arm.Keys.copy 27 0)
    (Two ExponentCountState) := by
  refine two_post ?_ copy27_ok
  refine (keyRegs_taint_ct copy27_taint (by decide) (by decide)).mono ?_ (fun _ _ _ => trivial)
  rintro s t ⟨p, left, right, sp⟩
  refine ⟨?_, sp⟩
  intro r hr
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact left.ready.r7.trans right.ready.r7.symm
  · exact left.ready.r8.trans right.ready.r8.symm
  · exact left.ready.r9.trans right.ready.r9.symm

end VG.Proof.Ffdh.Arm.ParameterCandidate
