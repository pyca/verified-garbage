module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTMontOne
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Nat.Basic
import Mathlib.Order.RelClasses

/-! Call exactly the selected shared RSA primality kernel and reuse its timing proof. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)
open VG.Proof.MillerRabin.Arm (RoundImpl LayoutLite PreparedLite roundPre roundPub)
open VG.Spec.Rsa.Mont (wOf)

structure SharedRoundStart (p : MontMathData) (s : State) : Prop where
  workspace : Workspace s p.base (8 * p.capacity)
  ptr : s.gpr .r0 = p.base
  length : s.gpr .r1 = BitVec.ofNat 32 p.capacity
  capacityBound : p.capacity < 2 ^ 32
  width : wOf s.mem (State.addr p.base) = p.words
  layout : LayoutLite s.mem (State.addr p.base) p.capacity
  prepared : PreparedLite s.mem (State.addr p.base)
  stackBelow : 56 ≤ s.sp.toNat
  belowSep : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩

private theorem sharedRoundPre {p : MontMathData} {s : State} (h : SharedRoundStart p s) :
    roundPre (s.callEntry.withRegions [] [⟨State.addr p.base, 8 * p.capacity⟩]) := by
  have r0entry : (s.callEntry.withRegions [] [⟨State.addr p.base, 8 * p.capacity⟩]).gpr .r0 = p.base := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h.ptr]
  have r1entry : (s.callEntry.withRegions [] [⟨State.addr p.base, 8 * p.capacity⟩]).gpr .r1 = BitVec.ofNat 32 p.capacity := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h.length]
  unfold roundPre
  rw [r0entry, r1entry, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.capacityBound]
  exact ⟨rfl, rfl, h.workspace.nowrap, h.stackBelow, h.belowSep, h.layout, h.prepared⟩

private theorem sharedRoundCovers {p : MontMathData} {s : State} (h : SharedRoundStart p s) :
    Covers [⟨State.addr p.base, 8 * p.capacity⟩] s.wr := by
  apply Covers.of_sub
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact ⟨_, h.workspace.writable, 0, by simp, by simp⟩

theorem sharedRoundCall_ct (v : RoundImpl) : RelCT isa (Two SharedRoundStart)
    (.call v.name v.code) (fun _ _ => True) := by
  intro s t trS trT u z h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  have call : RelCT isa (fun s t => SharedRoundStart p s ∧ SharedRoundStart p t ∧ s.sp = t.sp)
      (.call v.name v.code) (fun _ _ => True) := by
    refine RelCT.call v.verified.1 v.verified.2.1 [] [⟨State.addr p.base, 8 * p.capacity⟩] ?_
    intro a b h
    have coverA := sharedRoundCovers h.1
    have coverB := sharedRoundCovers h.2.1
    refine ⟨sharedRoundPre h.1, sharedRoundPre h.2.1, ?_, coverA.right, coverA, coverB.right, coverB⟩
    change roundPub _ _
    unfold roundPub
    simp only [State.withRegions_sp, State.callEntry_sp, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.withRegions_mem, State.callEntry_mem, h.1.ptr, h.2.1.ptr, h.1.length, h.2.1.length,
      h.1.width, h.2.1.width]
    exact ⟨h.2.2, trivial, trivial, trivial⟩
  exact call _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
