module

public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
public import VerifiedGarbage.Proof.Dsa.AArch64.ChildCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
public import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.AArch64.Child
import VerifiedGarbage.Proof.Dsa.AArch64.Parent
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.ChildCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
meta import VerifiedGarbage.Spec.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Child
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parent
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! ### `Dsa.AArch64.WorkspacesCT`, which only this module used -/

section

/-! # Constant time of initializing both Montgomery workspaces -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure WorkspacePublic extends ShapePublic where
  active : activeBytes ≤ extent
  lengths : Spec.Dsa.lengthsValid pBytes.length qBytes.length
  pOdd : Spec.Dsa.decodeBE pBytes % 2 = 1
  qOdd : Spec.Dsa.decodeBE qBytes % 2 = 1

def WorkspaceStage (p : WorkspacePublic) (s : State) : Prop :=
  Good s p.base p.extent outerWords 0 ∧ ShapeContext p.toShapePublic s

theorem ShapeContext.preserve {p : ShapePublic} {s t : State} {rs : List Reg}
    (h : ShapeContext p s) (hf : ∀ f : Field, word t.mem p.base f.offset = word s.mem p.base f.offset)
    (hm : InScr p.base p.extent s.mem t.mem) (hk : Keep rs s t) (hr : t.gpr .x0 = p.base) : ShapeContext p t :=
  ⟨h.scr.congr hk.wr, hr, (hf .p).trans h.pPointer, (hf .q).trans h.qPointer,
    (hf .pLen).trans h.pLength, (hf .qLen).trans h.qLength, (hf .digestLen).trans h.digestLength,
    h.pSource.congrK hm hk, h.qSource.congrK hm hk⟩

theorem workspaceParent_ct : RelCT isa (Two (fun (p : WorkspacePublic) s => ShapeContext p.toShapePublic s))
    (.block SignVerify.parent) (Two WorkspaceStage) := by
  refine two_post (two_map (fun p : WorkspacePublic => p.base) (fun _ _ h => h.x0) parent_ct) ?_
  intro p s h
  refine WP.mono (parent_ok h.scr h.x0 p.extentBound) fun t ⟨hg, hf, hk⟩ => ⟨hg, ?_⟩
  apply h.preserve _ _ hk hg.x0
  · intro f
    exact hf.word (Or.inr (Nat.le_trans (by decide) (VG.Proof.Dsa.field_bounds f).1))
      (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  · have hf' : Frm p.base [(48, 80)] s.mem t.mem := Frm.of_outside hf (by simp)
    apply InScr.of_frm hf'
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact Nat.le_trans (by decide) p.extentBound

def WorkspacePublic.child (p : WorkspacePublic) (isP : Bool) : ChildPublic where
  x := ⟨p.base, p.extent, if isP then pWorkspace else qWorkspace, outerWords,
    ((if isP then p.pBytes else p.qBytes).length + 7) / 8⟩
  ptr := if isP then p.pPointer else p.qPointer
  len := (if isP then p.pBytes else p.qBytes).length
  extent := p.extentBound
  offset := by
    cases isP
    · change qWorkspace < 2 ^ 16; decide
    · change pWorkspace < 2 ^ 16; decide
  lo := by
    cases isP
    · change slot outerWords 8 ≤ qWorkspace; decide
    · change slot outerWords 8 ≤ pWorkspace; decide
  hi := by
    obtain ⟨_, _, _, _, _, hp, hq, _⟩ := VG.Proof.Dsa.workspace_bounds p.lengths
    cases isP
    · exact Nat.le_trans hq p.active
    · exact Nat.le_trans hp (Nat.le_trans (by decide) p.active)
  widthPositive := by
    obtain ⟨hp, _, hq, _⟩ := VG.Proof.Dsa.workspace_bounds p.lengths
    cases isP
    · exact hq
    · exact hp
  widthParent := by
    obtain ⟨_, hp, _, hq, _⟩ := VG.Proof.Dsa.workspace_bounds p.lengths
    cases isP
    · exact hq
    · exact hp
  widthBound := by change outerWords < 2 ^ 30; decide
  positive := by cases isP; exact p.qPositive; exact p.pPositive
  lengthBound := by
    have hl := p.lengths
    change (if isP then p.pBytes else p.qBytes).length < 2 ^ 31
    cases isP <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rcases hl with ⟨h1, h2⟩ | ⟨h1, h2 | h2 | h2⟩ | ⟨h1, h2⟩ <;> omega_arith
  width := rfl

def workspaceOperand (isP : Bool) : Operand :=
  if isP then ⟨.input .p, .pLen⟩ else ⟨.input .q, .qLen⟩

theorem workspaceChild_pre {p : WorkspacePublic} {s : State} (h : WorkspaceStage p s) (isP : Bool) :
    ChildPre (workspaceOperand isP) (p.child isP) s := by
  refine ⟨⟨0, h.1⟩, (if isP then p.pBytes else p.qBytes), ?_⟩
  cases isP
  · exact ⟨h.2.qPointer, h.2.qLength, h.2.qSource, rfl⟩
  · exact ⟨h.2.pPointer, h.2.pLength, h.2.pSource, rfl⟩

theorem workspaceChild_ct (isP : Bool) : RelCT isa (Two WorkspaceStage)
    (SignVerify.child (if isP then pWorkspace else qWorkspace) (workspaceOperand isP)) (Two WorkspaceStage) := by
  have ha : pointerFits (workspaceOperand isP).pointer := by cases isP <;> trivial
  have hc : RelCT isa (Two (fun p s => ChildPre (workspaceOperand isP) p s ∧
      p.x.o = (if isP then pWorkspace else qWorkspace)))
      (SignVerify.child (if isP then pWorkspace else qWorkspace) (workspaceOperand isP)) (fun _ _ => True) := by
    cases isP <;> exact child_ct _ (by trivial) _ (by taint_decide)
  refine two_post (two_map (fun p : WorkspacePublic => p.child isP)
    (fun _ _ h => ⟨workspaceChild_pre h isP, rfl⟩) hc) ?_
  intro p s h
  let c := p.child isP
  obtain ⟨_, bs, hp, hl, hs, hlen⟩ := workspaceChild_pre h isP
  have ho : Spec.Dsa.decodeBE bs % 2 = 1 := by
    -- The bytes supplied by workspaceChild_pre are fixed by their source.
    have he : bs = (if isP then p.pBytes else p.qBytes) := by
      apply List.ext_getElem
      · simpa only [c, WorkspacePublic.child] using hlen
      · intro i hi hj
        cases isP
        · exact (hs.val i hi).symm.trans (h.2.qSource.val i hj)
        · exact (hs.val i hi).symm.trans (h.2.pSource.val i hj)
    rw [he]
    cases isP
    · exact p.qOdd
    · exact p.pOdd
  refine WP.mono (child_ok h.1 c.extent c.offset c.lo c.hi c.widthPositive c.widthParent c.widthBound
    (workspaceOperand isP) ha hp hl hs (hlen ▸ c.positive) (hlen ▸ c.lengthBound)
    (by rw [hlen]; exact c.width) ho) fun t ⟨_, hg, _, hf, hk⟩ => ⟨hg, ?_⟩
  apply h.2.preserve _ _ hk hg.x0
  · intro f
    apply init_word hf
    · have := VG.Proof.Dsa.field_bounds f
      cases isP
      · exact Nat.le_trans this.2 (show pWorkspace ≤ qWorkspace by decide)
      · exact this.2
    · exact Or.inr (Nat.le_trans (by decide) (VG.Proof.Dsa.field_bounds f).1)
    · have := c.offset; omega_using [this]
  · apply InScr.of_frm hf
    intro r hr
    simp only [initRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Nat.le_trans (by decide) p.extentBound
    · have hh := c.hi
      change c.x.o + slot c.x.wx 8 ≤ p.extent
      change c.x.o + slot c.x.wx 8 + tabBytes c.x.wx ≤ p.extent at hh
      omega_using [hh]

theorem workspaces_ct : RelCT isa (Two (fun (p : WorkspacePublic) s => ShapeContext p.toShapePublic s))
    SignVerify.workspaces (fun _ _ => True) := by
  exact (RelCT.seq workspaceParent_ct (RelCT.seq (workspaceChild_ct true) (workspaceChild_ct false))).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.Dsa.AArch64

end

end

/-! # Relating independently initialized workspaces without assuming scratch equality -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure InitializationPublic where
  layout : ExecutionLayout
  pBytes : List Byte
  qBytes : List Byte
  pLength : pBytes.length = layout.pLen
  qLength : qBytes.length = layout.qLen
  pValue : Spec.Dsa.decodeBE pBytes = layout.modulus
  qValue : Spec.Dsa.decodeBE qBytes = layout.subgroup
  pOdd : layout.modulus % 2 = 1
  qOdd : layout.subgroup % 2 = 1

structure InitializationPre (p : InitializationPublic) (s : State) : Prop where
  scratch : Scr s p.layout.base usedBytes
  x0 : s.gpr .x0 = p.layout.base
  fields : ∀ f, word s.mem p.layout.base f.offset = p.layout.fields f
  pSource : Src s p.layout.base usedBytes (p.layout.fields .p) p.pBytes
  qSource : Src s p.layout.base usedBytes (p.layout.fields .q) p.qBytes

def InitializationPublic.workspace (p : InitializationPublic) : WorkspacePublic where
  base := p.layout.base
  extent := usedBytes
  pPointer := p.layout.fields .p
  qPointer := p.layout.fields .q
  pBytes := p.pBytes
  qBytes := p.qBytes
  digestLen := (p.layout.fields .digestLen).toNat
  extentBound := by decide
  pPositive := by rw [p.pLength]; have := p.layout.widths; omega_using [this]
  qPositive := by rw [p.qLength]; exact p.layout.widths.1
  pBound := by rw [p.pLength]; have := p.layout.widths; omega_using [this]
  qBound := by rw [p.qLength]; have := p.layout.widths; omega_using [this]
  digestBound := (p.layout.fields .digestLen).isLt
  active := by decide
  lengths := by rw [p.pLength, p.qLength]; exact p.layout.lengths
  pOdd := by rw [p.pValue]; exact p.pOdd
  qOdd := by rw [p.qValue]; exact p.qOdd

def InitializationDone (p : InitializationPublic) (s : State) : Prop :=
  ∃ pi qi, Ready (p.layout.withInverses pi qi) s ∧
    word s.mem p.layout.base Field.mask.offset = p.layout.fields .mask

theorem initialization_ct : RelCT isa (Two InitializationPre) SignVerify.workspaces (Two InitializationDone) := by
  refine two_post (two_map InitializationPublic.workspace (fun p s h => ?_) workspaces_ct) ?_
  · refine ⟨h.scratch, h.x0, h.fields .p, h.fields .q, ?_, ?_, ?_, h.pSource, h.qSource⟩
    · change word s.mem p.layout.base Field.pLen.offset = BitVec.ofNat 64 p.pBytes.length
      rw [p.pLength]; exact (h.fields .pLen).trans p.layout.pLength
    · change word s.mem p.layout.base Field.qLen.offset = BitVec.ofNat 64 p.qBytes.length
      rw [p.qLength]; exact (h.fields .qLen).trans p.layout.qLength
    · change word s.mem p.layout.base Field.digestLen.offset = BitVec.ofNat 64 (p.layout.fields .digestLen).toNat
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.fields .digestLen
  · intro p s h
    exact WP.mono (workspacesReady_ok h.scratch h.x0 h.fields h.pSource h.qSource
      p.pLength p.qLength p.pValue p.qValue p.pOdd p.qOdd)
      fun t ⟨pi, qi, hr, _, hm, _⟩ => ⟨pi, qi, hr, hm.trans (h.fields .mask)⟩

end VG.Proof.Dsa.AArch64
