module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTDecompose
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentSigma
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Decompose
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ExponentSigma
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Carry public decomposition metadata into the bounded exponent shift. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Keys (num)
open VG.Proof.Ffdh.Arm.KeySearch

structure DecomposeDone (p : DecomposeData) (s : State) : Prop where
  start : DecomposeStart p s
  saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 (Spec.Rsa.splitTwos (p.modulus - 1)).1

private theorem decomposeDone_ok (p : DecomposeData) (s : State) (h : DecomposeStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose s (DecomposeDone p) := by
  refine WP.mono (expDecompose_ok h.workspace h.ready h.data h.stack h.separate h.number h.large h.odd) ?_
  rintro t ⟨ready, data, _, saved, arrays, _, _, rest⟩
  exact ⟨⟨h.workspace.congr rest.wr, ready, data, by rw [rest.sp]; exact h.stack.congr rest.wr,
    by rw [rest.sp]; exact h.separate, (arrays 0 (by decide) (by decide)).trans h.number, h.large, h.odd⟩, saved⟩

theorem decomposeDone_ct : RelCT isa (Two DecomposeStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose (Two DecomposeDone) :=
  two_post expDecompose_ct decomposeDone_ok

private theorem sigmaReady_ok (p : DecomposeData) (s : State) (h : DecomposeDone p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma s
      (ExponentCountState ⟨p.math, countShift (Spec.Rsa.splitTwos (p.modulus - 1)).1⟩) := by
  refine WP.mono (exponentSigma_ok h.start.stack h.saved) ?_
  rintro t ⟨mem, rest⟩
  have eqWork : WorkspaceEq (State.addr p.math.base) (8 * p.math.capacity) s.mem t.mem := by
    rw [mem]
    exact stackWrite_workspaceEq h.start.workspace h.start.stack h.start.separate (by decide) _
  exact ⟨h.start.workspace.congr rest.wr,
    h.start.ready.rest rest (by decide) (by decide) (by decide), h.start.data.after_workspaceEq eqWork,
    by rw [rest.sp]; exact h.start.stack.congr rest.wr,
    by rw [rest.sp]; exact h.start.separate,
    (countShift_bounds _).1, (countShift_bounds _).2, by rw [rest.sp, mem, Mem.readW_writeW_self32]⟩

theorem sigmaReady_ct : RelCT isa (Two DecomposeDone)
    VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma (Two ExponentCountState) := by
  have trace : RelCT isa (Two DecomposeDone)
      VG.Impl.Ffdh.Arm.ParameterCandidate.exponentSigma (fun _ _ => True) :=
    (two_map (fun p => (Spec.Rsa.splitTwos (p.modulus - 1)).1)
      (fun _ _ h => ⟨h.start.stack, h.saved⟩) exponentSigma_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)
  exact (two_post trace sigmaReady_ok).mono (fun _ _ h => h)
    (fun _ _ ⟨p, left, right, sp⟩ => ⟨⟨p.math, countShift (Spec.Rsa.splitTwos (p.modulus - 1)).1⟩, left, right, sp⟩)

end VG.Proof.Ffdh.Arm.ParameterCandidate
