module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CacheMemory

/-! Regions of a key-generation call nested inside the retry controller. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

abbrev rX (p : KeyPublic sampling) : Region := ⟨State.addr p.xp, p.len⟩
abbrev rY (p : KeyPublic sampling) : Region := ⟨State.addr p.yp, p.len⟩
abbrev rUsed (p : KeyPublic sampling) : Region := ⟨State.addr p.up, 8⟩
abbrev rDomain (p : KeyPublic sampling) : Region := ⟨State.addr p.dp, p.dlen⟩
abbrev rRandom (p : KeyPublic sampling) : Region := ⟨State.addr p.rp, p.randLen⟩
abbrev rScratch (p : KeyPublic sampling) : Region := ⟨State.addr p.scratch, p.capacity * 8⟩
abbrev rControl (p : KeyPublic sampling) : Region := ⟨State.addr p.control, 128⟩
abbrev rSaved (p : KeyPublic sampling) : Region := ⟨State.addr (p.sp - BitVec.ofNat 32 24), 24⟩
abbrev callSp (p : KeyPublic sampling) : BitVec 32 := p.sp - BitVec.ofNat 32 (24 + sampling.argumentBytes)
abbrev rArguments (p : KeyPublic sampling) : Region := ⟨State.addr (callSp p), sampling.argumentBytes⟩
abbrev rCallStack (p : KeyPublic sampling) : Region := FrameStack.belowA (callSp p) 176

def contextRegions (p : KeyPublic sampling) : List Region :=
  if sampling.cachedContext then [rContext p] else []

def callChanges (p : KeyPublic sampling) : List Region := [rX p, rY p, rScratch p, rArguments p, rCallStack p]

theorem KeyInput.write_regions {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    s.wr = [rX p, rY p, rUsed p, rScratch p, rControl p] := by
  rw [h.layout.wr, writes, h.x_eq, h.y_eq, ← h.2.1]
  rfl

theorem KeyInput.read_regions {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    s.rd = [rDomain p, rRandom p] ++ contextRegions p ++ [inArgs sampling s] ++ KeyConstants.regions sampling p.tablePtr := by
  rw [h.layout.rd, reads, h.constant_regions, ← h.2.1]
  cases sampling <;> rfl

theorem KeyInput.output_regions_disjoint {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    (rX p).Disjoint (rY p) ∧ (rX p).Disjoint (rScratch p) ∧
      (rY p).Disjoint (rScratch p) ∧ (rControl p).Disjoint (rX p) ∧
      (rControl p).Disjoint (rY p) ∧ (rControl p).Disjoint (rScratch p) := by
  have pairs := h.layout.pairwise
  rw [← h.layout.wr, h.write_regions] at pairs
  have indexed := List.pairwise_iff_getElem.mp pairs
  exact ⟨indexed 0 1 (by simp) (by simp) (by decide),
    indexed 0 3 (by simp) (by simp) (by decide),
    indexed 1 3 (by simp) (by simp) (by decide),
    (indexed 0 4 (by simp) (by simp) (by decide)).symm,
    (indexed 1 4 (by simp) (by simp) (by decide)).symm,
    (indexed 3 4 (by simp) (by simp) (by decide)).symm⟩

theorem KeyInput.stack_separate {p : KeyPublic sampling} {s : State} (h : KeyInput p s)
    {r : Region} (member : r ∈ s.wr ++ s.rd) :
    (FrameStack.belowA p.sp (stackUse sampling)).Disjoint r := by
  have sep := h.layout.stack r (by rw [← h.layout.wr, ← h.layout.rd]; exact member)
  have fit := h.bounds.stackFits
  rw [← h.2.1] at fit ⊢
  change (stackUse sampling) ≤ s.sp.toNat at fit
  change (FrameStack.belowA s.sp (stackUse sampling)).Disjoint r
  rwa [FrameStack.belowA, FrameStack.addr_sub' fit]

theorem KeyInput.constants_read {p : KeyPublic sampling} {s : State} (h : KeyInput p s)
    {table : Region} (member : table ∈ KeyConstants.regions sampling p.tablePtr) : table ∈ s.rd := by
  rw [h.read_regions]
  exact List.mem_append_right _ member

theorem KeyInput.constants_write {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    ∀ table ∈ KeyConstants.regions sampling p.tablePtr, ∀ r ∈ s.wr, table.Disjoint r := by
  intro table member r hr
  apply Region.Disjoint.symm
  exact h.layout.separate r (by rw [← h.layout.wr]; exact hr) table
    (by rw [← h.layout.rd]; exact h.constants_read member)

theorem KeyInput.constants_control {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    ∀ table ∈ KeyConstants.regions sampling p.tablePtr, table.Disjoint (rControl p) := by
  intro table member
  exact h.constants_write table member _ (by rw [h.write_regions]; simp)

theorem KeyInput.constants_stack {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    ∀ table ∈ KeyConstants.regions sampling p.tablePtr, table.Disjoint (FrameStack.belowA p.sp (stackUse sampling)) := by
  intro table member
  exact (h.stack_separate (List.mem_append_right s.wr (h.constants_read member))).symm


theorem arguments_sub {p : KeyPublic sampling} (fit : stackUse sampling ≤ p.sp.toNat) :
    (rArguments p).Sub (FrameStack.belowA p.sp (stackUse sampling)) := by
  have address : p.sp - 24#32 - BitVec.ofNat 32 sampling.argumentBytes = callSp p := by
    rw [BitVec.sub_sub]
    simp only [callSp, BitVec.ofNat_add]
  have sub := FrameStack.belowA_inner (sp := p.sp) (a := sampling.argumentBytes) (k := 24)
    (by cases sampling <;> decide : sampling.argumentBytes + 24 ≤ stackUse sampling) fit
  change (⟨State.addr (p.sp - 24#32 - BitVec.ofNat 32 sampling.argumentBytes),
    sampling.argumentBytes⟩ : Region).Sub _ at sub
  rw [address] at sub
  exact sub

theorem callStack_sub {p : KeyPublic sampling} (fit : stackUse sampling ≤ p.sp.toNat) :
    (rCallStack p).Sub (FrameStack.belowA p.sp (stackUse sampling)) :=
  FrameStack.belowA_inner
    (by cases sampling <;> decide : 176 + (24 + sampling.argumentBytes) ≤ stackUse sampling) fit

theorem saved_arguments_separate {p : KeyPublic sampling} (fit : stackUse sampling ≤ p.sp.toNat) :
    (rSaved p).Disjoint (rArguments p) := by
  change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at fit
  rw [rSaved, rArguments, callSp, FrameStack.addr_sub' (by omega : 24 ≤ p.sp.toNat),
    FrameStack.addr_sub' (by omega : 24 + sampling.argumentBytes ≤ p.sp.toNat)]
  have address : State.addr p.sp - BitVec.ofNat 64 (24 + sampling.argumentBytes) =
      (State.addr p.sp - 24#64) - BitVec.ofNat 64 sampling.argumentBytes := by
    rw [BitVec.sub_sub, BitVec.ofNat_add]
  rw [address]
  exact Offset.base_disjoint_below _ (by have := argumentBytes_max sampling; omega)

theorem saved_callStack_separate {p : KeyPublic sampling} (fit : stackUse sampling ≤ p.sp.toNat) :
    (rSaved p).Disjoint (rCallStack p) := by
  change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at fit
  have room : 176 ≤ (callSp p).toNat := by
    rw [callSp, FrameStack.sub_toNat' (by omega : 24 + sampling.argumentBytes ≤ p.sp.toNat)]
    omega
  rw [rSaved, rCallStack, FrameStack.belowA, FrameStack.addr_sub' room,
    FrameStack.addr_sub' (by omega : 24 ≤ p.sp.toNat)]
  have savedAddr : State.addr p.sp - 24#64 =
      State.addr (callSp p) + BitVec.ofNat 64 sampling.argumentBytes := by
    rw [callSp, FrameStack.addr_sub' (by omega : 24 + sampling.argumentBytes ≤ p.sp.toNat)]
    rw [show BitVec.ofNat 64 (24 + sampling.argumentBytes) =
      24#64 + BitVec.ofNat 64 sampling.argumentBytes from BitVec.ofNat_add _ _,
      ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [savedAddr]
  exact Offset.disjoint_below _ (by have := argumentBytes_max sampling; omega)

end VG.Proof.Ffdh.Arm.KeySearch
