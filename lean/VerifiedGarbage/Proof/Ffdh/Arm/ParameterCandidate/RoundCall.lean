module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Data.Nat.Basic
import Mathlib.Order.RelClasses

/-! Call the existing RSA/shared compact Miller–Rabin implementation with
its exact selected name and body, and its existing 56-byte stack bound. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Spec.Rsa.Mont (numAt wOf)
open VG.Proof.MillerRabin.Arm (RoundImpl LayoutLite PreparedLite KeepsLite roundPre roundPost)

theorem sharedRoundCall_ok (v : RoundImpl) {s : State} {base : BitVec 32} {capacity w witness : Nat}
    (workspace : Workspace s base (8 * capacity))
    (ptr : s.gpr .r0 = base) (length : s.gpr .r1 = BitVec.ofNat 32 capacity)
    (capacityBound : capacity < 2 ^ 32)
    (width : wOf s.mem (State.addr base) = w)
    (layout : LayoutLite s.mem (State.addr base) capacity) (prepared : PreparedLite s.mem (State.addr base))
    (stack : 56 ≤ s.sp.toNat)
    (separate : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (encoded : numAt s.mem (State.addr base) w 5 =
      witness % numAt s.mem (State.addr base) w 0 * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0) :
    WP isa (.call v.name v.code) s fun t =>
      (t.gpr .r0).toNat = (if Spec.MillerRabin.round (numAt s.mem (State.addr base) w 0) witness then 1 else 0) ∧
      KeepsLite (State.addr base) capacity w s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * capacity⟩, FrameStack.belowA s.sp 56] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have r0entry : (s.callEntry.withRegions [] [⟨State.addr base, 8 * capacity⟩]).gpr .r0 = base := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), ptr]
  have r1entry : (s.callEntry.withRegions [] [⟨State.addr base, 8 * capacity⟩]).gpr .r1 =
      BitVec.ofNat 32 capacity := by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), length]
  have capValue : (BitVec.ofNat 32 capacity).toNat = capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt capacityBound]
  have pre : roundPre (s.callEntry.withRegions [] [⟨State.addr base, 8 * capacity⟩]) := by
    unfold roundPre
    rw [r0entry, r1entry, capValue]
    exact ⟨rfl, rfl, workspace.nowrap, stack, separate, layout, prepared⟩
  have covers : Covers [⟨State.addr base, 8 * capacity⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨_, workspace.writable, 0, by simp, by simp⟩
  refine FrameStack.WP.callF v.verified.1 pre covers.right covers (by have := v.stack; omega)
    fun t rd wr sp frame _ post => ?_
  change roundPost _ _ at post
  unfold roundPost at post
  rw [r0entry, r1entry, capValue] at post
  simp only [State.withRegions_mem, State.callEntry_mem, width] at post
  refine ⟨post.1 witness encoded, post.2, ?_, ?_⟩
  · refine frame.sub ?_
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, FrameStack.belowA_sub v.stack stack⟩
  · refine ⟨?_, rd, wr, sp⟩
    intro r hr
    cases r <;> simp [roundClobbers] at hr

end VG.Proof.Ffdh.Arm.ParameterCandidate
