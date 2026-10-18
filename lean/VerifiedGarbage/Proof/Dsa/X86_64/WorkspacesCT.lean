module

public import VerifiedGarbage.Proof.Dsa.X86_64.ChildCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ChildCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
public import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.MdStream.Spec
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.MdStream.Spec

/-! # Constant time of initializing both Montgomery workspaces -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure WorkspacePublic extends ShapePublic where
  active : activeBytes ≤ extent
  lengths : Spec.Dsa.lengthsValid pBytes.length qBytes.length
  pOdd : Spec.Dsa.decodeBE pBytes % 2 = 1
  qOdd : Spec.Dsa.decodeBE qBytes % 2 = 1

def WorkspaceStage (p : WorkspacePublic) (s : State) : Prop :=
  Good s p.base p.extent outerWords 0 ∧ ShapeContext p.toShapePublic s

theorem ShapeContext.preserve {p : ShapePublic} {s t : State} {rs : List Reg}
    (h : ShapeContext p s) (hf : ∀ f : Field, word t.mem p.base f.offset = word s.mem p.base f.offset)
    (hm : InScr p.base p.extent s.mem t.mem) (hk : Keep rs s t) (hr : t.gpr .rdi = p.base) : ShapeContext p t :=
  ⟨h.scr.congr hk.2.2, hr, (hf .p).trans h.pPointer, (hf .q).trans h.qPointer,
    (hf .pLen).trans h.pLength, (hf .qLen).trans h.qLength, (hf .digestLen).trans h.digestLength,
    h.pSource.congrK hm hk, h.qSource.congrK hm hk⟩

theorem workspaceParent_ct : RelCT isa (Two (fun (p : WorkspacePublic) s => ShapeContext p.toShapePublic s))
    (.block SignVerify.parent) (Two WorkspaceStage) := by
  refine two_post (two_map (fun p : WorkspacePublic => p.base) (fun _ _ h => h.rdi) parent_ct) ?_
  intro p s h
  refine WP.mono (parent_ok h.scr h.rdi p.extentBound) fun t ⟨hg, hf, hk⟩ => ⟨hg, ?_⟩
  apply h.preserve _ _ hk hg.rdi
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
    · change qWorkspace < 2 ^ 31; decide
    · change pWorkspace < 2 ^ 31; decide
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
      rcases hl with ⟨h1, h2⟩ | ⟨h1, h2 | h2 | h2⟩ | ⟨h1, h2⟩ <;> omega
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
  apply h.2.preserve _ _ hk hg.rdi
  · intro f
    apply init_word hf
    · have := VG.Proof.Dsa.field_bounds f
      cases isP
      · exact Nat.le_trans this.2 (show pWorkspace ≤ qWorkspace by decide)
      · exact this.2
    · exact Or.inr (Nat.le_trans (by decide) (VG.Proof.Dsa.field_bounds f).1)
    · have := c.offset; omega
  · apply InScr.of_frm hf
    intro r hr
    simp only [initRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Nat.le_trans (by decide) p.extentBound
    · have hh := c.hi
      change c.x.o + slot c.x.wx 8 ≤ p.extent
      change c.x.o + slot c.x.wx 8 + tabBytes c.x.wx ≤ p.extent at hh
      omega

theorem workspaces_ct : RelCT isa (Two (fun (p : WorkspacePublic) s => ShapeContext p.toShapePublic s))
    SignVerify.workspaces (fun _ _ => True) := by
  exact (RelCT.seq workspaceParent_ct (RelCT.seq (workspaceChild_ct true) (workspaceChild_ct false))).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.Dsa.X86_64
