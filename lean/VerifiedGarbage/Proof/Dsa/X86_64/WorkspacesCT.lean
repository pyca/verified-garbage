module

public import VerifiedGarbage.Proof.Dsa.X86_64.ChildCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ChildCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
public import VerifiedGarbage.Spec.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Tactic.Set
meta import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.X86_64.Child
meta import VerifiedGarbage.Proof.Dsa.X86_64.Child
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parent
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShape
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Parity
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTail
import VerifiedGarbage.Proof.Dsa.X86_64.Store
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.DomainShape
meta import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Masks
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parity
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
meta import VerifiedGarbage.Proof.Dsa.X86_64.Setup
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTail
meta import VerifiedGarbage.Proof.Dsa.X86_64.Store
meta import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.MdStream.Spec
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Sha256.Stream

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
