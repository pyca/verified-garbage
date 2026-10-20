module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract

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
abbrev callSp (p : KeyPublic sampling) : BitVec 32 := p.sp - BitVec.ofNat 32 56
abbrev rArguments (p : KeyPublic sampling) : Region := ⟨State.addr (callSp p), 32⟩
abbrev rCallStack (p : KeyPublic sampling) : Region := FrameStack.belowA (callSp p) 176

def callChanges (p : KeyPublic sampling) : List Region := [rX p, rY p, rScratch p, rArguments p, rCallStack p]

theorem KeyInput.write_regions {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    s.wr = [rX p, rY p, rUsed p, rScratch p, rControl p] := by
  rw [h.layout.wr, writes, h.x_eq, h.y_eq, ← h.2.1]
  rfl

theorem KeyInput.read_regions {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    s.rd = [rDomain p, rRandom p, inArgs s] ++ KeyConstants.regions sampling p.tablePtr := by
  rw [h.layout.rd, reads, h.constant_regions, ← h.2.1]
  rfl

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
    (FrameStack.belowA p.sp stackUse).Disjoint r := by
  have sep := h.layout.stack r (by rw [← h.layout.wr, ← h.layout.rd]; exact member)
  have fit := h.bounds.stackFits
  rw [← h.2.1] at fit ⊢
  change stackUse ≤ s.sp.toNat at fit
  change (FrameStack.belowA s.sp stackUse).Disjoint r
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
    ∀ table ∈ KeyConstants.regions sampling p.tablePtr, table.Disjoint (FrameStack.belowA p.sp stackUse) := by
  intro table member
  exact (h.stack_separate (List.mem_append_right s.wr (h.constants_read member))).symm


theorem arguments_sub {p : KeyPublic sampling} (fit : stackUse ≤ p.sp.toNat) :
    (rArguments p).Sub (FrameStack.belowA p.sp stackUse) := by
  have address : p.sp - 24#32 - 32#32 = callSp p := by rw [BitVec.sub_sub]; rfl
  have sub := FrameStack.belowA_inner (sp := p.sp) (a := 32) (k := 24)
    (by decide : 32 + 24 ≤ stackUse) fit
  change (⟨State.addr (p.sp - 24#32 - 32#32), 32⟩ : Region).Sub _ at sub
  rw [address] at sub
  exact sub

theorem callStack_sub {p : KeyPublic sampling} (fit : stackUse ≤ p.sp.toNat) :
    (rCallStack p).Sub (FrameStack.belowA p.sp stackUse) :=
  FrameStack.belowA_inner (by decide : 176 + 56 ≤ stackUse) fit

theorem saved_arguments_separate {p : KeyPublic sampling} (fit : stackUse ≤ p.sp.toNat) :
    (rSaved p).Disjoint (rArguments p) := by
  change 232 ≤ p.sp.toNat at fit
  rw [rSaved, rArguments, callSp, FrameStack.addr_sub' (by omega : 24 ≤ p.sp.toNat),
    FrameStack.addr_sub' (by omega : 56 ≤ p.sp.toNat)]
  have address : State.addr p.sp - 56#64 = (State.addr p.sp - 24#64) - 32#64 := by
    rw [BitVec.sub_sub]; rfl
  rw [address]
  exact Offset.base_disjoint_below _ (by decide)

theorem saved_callStack_separate {p : KeyPublic sampling} (fit : stackUse ≤ p.sp.toNat) :
    (rSaved p).Disjoint (rCallStack p) := by
  change 232 ≤ p.sp.toNat at fit
  have room : 176 ≤ (callSp p).toNat := by
    rw [callSp, FrameStack.sub_toNat' (by omega : 56 ≤ p.sp.toNat)]; omega
  rw [rSaved, rCallStack, FrameStack.belowA, FrameStack.addr_sub' room,
    FrameStack.addr_sub' (by omega : 24 ≤ p.sp.toNat)]
  have savedAddr : State.addr p.sp - 24#64 = State.addr (callSp p) + 32#64 := by
    rw [callSp, FrameStack.addr_sub' (by omega : 56 ≤ p.sp.toNat)]
    rw [show (56#64) = 24#64 + 32#64 by rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [savedAddr]
  exact Offset.disjoint_below _ (by decide)

end VG.Proof.Ffdh.Arm.KeySearch
