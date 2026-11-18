module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningInput
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.Dsa.X86_64.SignBody
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.X86_64.Execution
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.X86_64.Child
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86_64.InitFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import VerifiedGarbage.Proof.Dsa.X86_64.ChildCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ChildCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
meta import VerifiedGarbage.Spec.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Child
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parent

/-! ### `Dsa.X86_64.SigningOperands`, which the modules that import this one used -/

section

/-! ### `Dsa.X86_64.WorkspacesCT`, which only this module used -/

section

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
  apply h.2.preserve _ _ hk hg.rdi
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

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.WorkspaceBridge`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.WorkspaceReady`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Workspaces`, which only this module used -/

section

/-! # Initializing both DSA moduli in the shared scratch allocation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def workspaceRanges (wp wq : Nat) : List (Nat × Nat) :=
  [(48, 80)] ++ initRanges pWorkspace wp ++ initRanges qWorkspace wq

theorem workspaces_ok {s : State} {B pp qp : Addr} {Z : Nat} {p q : List Byte}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : activeBytes ≤ Z)
    (hp : word s.mem B Field.p.offset = pp) (hq : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p.length)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q.length)
    (hps : Src s B Z pp p) (hqs : Src s B Z qp q)
    (hlens : Spec.Dsa.lengthsValid p.length q.length)
    (hpodd : Spec.Dsa.decodeBE p % 2 = 1) (hqodd : Spec.Dsa.decodeBE q % 2 = 1) :
    WP isa SignVerify.workspaces s fun t => ∃ pmi qmi : BitVec 64,
      Good t B Z outerWords 0 ∧
      ChildReady t.mem B pWorkspace ((p.length + 7) / 8) (Spec.Dsa.decodeBE p) pmi ∧
      ChildReady t.mem B qWorkspace ((q.length + 7) / 8) (Spec.Dsa.decodeBE q) qmi ∧
      Frm B (workspaceRanges ((p.length + 7) / 8) ((q.length + 7) / 8)) s.mem t.mem ∧
      Keep coreRegs s t := by
  obtain ⟨hp2, hp48, hq2, hq48, hpLo, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds hlens
  have hlengths : 1 ≤ p.length ∧ p.length < 2 ^ 31 ∧ 1 ≤ q.length ∧ q.length < 2 ^ 31 := by
    unfold Spec.Dsa.lengthsValid at hlens
    omega_using [hlens]
  have hparent : pWorkspace ≤ Z := Nat.le_trans (by decide) hZ
  unfold SignVerify.workspaces seqs
  refine WP.seq (WP.mono (parent_ok hs hdi hparent) fun u ⟨hgu, hfu, hku⟩ => ?_)
  have uf : Frm B [(48, 80)] s.mem u.mem := Frm.of_outside hfu (by simp)
  have ufield (f : Field) : word u.mem B f.offset = word s.mem B f.offset :=
    hfu.word (Or.inr (Nat.le_trans (by decide) (VG.Proof.Dsa.field_bounds f).1))
      (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  have usrc {ptr : Addr} {bs : List Byte} (hsrc : Src s B Z ptr bs) : Src u B Z ptr bs := by
    apply hsrc.congrK _ hku
    apply InScr.of_frm uf
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact Nat.le_trans (by decide) hparent
  refine WP.seq (WP.mono (child_ok hgu hparent (by decide) hpLo (Nat.le_trans hpHi (Nat.le_trans (by decide) hZ))
    hp2 hp48 (by decide) ⟨.input .p, .pLen⟩ (by trivial)
    ((ufield .p).trans hp) ((ufield .pLen).trans hpl) (usrc hps)
    hlengths.1 hlengths.2.1 rfl hpodd) fun v ⟨pmi, hgv, hpr, hfv, hkv⟩ => ?_)
  have vfield (f : Field) : word v.mem B f.offset = word u.mem B f.offset :=
    init_word hfv (VG.Proof.Dsa.field_bounds f).2
      (Or.inr (Nat.le_trans (by decide) (VG.Proof.Dsa.field_bounds f).1)) (by decide)
  have vqs := init_source hfv hkv (Nat.le_trans (by decide) hparent) (by omega_using [hZ, hpHi, hqHi]) (usrc hqs)
  have hqLo : slot outerWords 8 ≤ qWorkspace := by decide
  refine WP.mono (child_ok hgv hparent (by decide) hqLo (Nat.le_trans hqHi hZ)
    hq2 hq48 (by decide) ⟨.input .q, .qLen⟩ (by trivial)
    ((vfield .q).trans ((ufield .q).trans hq)) ((vfield .qLen).trans ((ufield .qLen).trans hql)) vqs
    hlengths.2.2.1 hlengths.2.2.2 rfl hqodd) fun t ⟨qmi, hgt, hqr, hft, hkt⟩ => ?_
  have hprt := init_ready hft hpr (by decide) (by have := hs.nowrap; omega_using [hZ, hpHi, hqHi, this]) (Or.inl (by omega_using [hpHi]))
  exact ⟨pmi, qmi, hgt, hprt, hqr, (uf.append hfv).append hft,
    ((hku.trans hkv).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end


/-! # Establishing the persistent DSA context from caller scratch -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem workspace_field {B : Addr} {wp wq : Nat} {mem mem' : Mem}
    (hf : Frm B (workspaceRanges wp wq) mem mem') (f : Field) :
    word mem' B f.offset = word mem B f.offset := by
  have hb := VG.Proof.Dsa.field_bounds f
  have hpq : pWorkspace ≤ qWorkspace := by decide
  apply hf.word_eq _ (Nat.le_trans hb.2 (by decide))
  intro range hr
  simp only [workspaceRanges, initRanges, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · right; omega_using [hb]
  · right; omega_using [hb]
  · exact Or.inl hb.2
  · right; omega_using [hb]
  · left; omega_using [hb, hpq]

theorem workspace_outside {L : ExecutionLayout} {mem mem' : Mem}
    (hf : Frm L.base (workspaceRanges L.pWords L.qWords) mem mem') :
    Outside L.base 48 (activeBytes - 48) mem mem' := by
  obtain ⟨_, _, _, _, _, hphi, hqhi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ qWorkspace at hphi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqhi
  have hqa : qWorkspace ≤ activeBytes := by decide
  have hlo : 48 ≤ pWorkspace ∧ 48 ≤ qWorkspace ∧ 144 ≤ activeBytes := by decide
  intro x hx
  apply hf x
  intro range hr
  simp only [workspaceRanges, initRanges, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only at * <;> omega_arith

theorem workspacesReady_ok {L : ExecutionLayout} {s : State} {pb qb : List Byte}
    (hs : Scr s L.base usedBytes) (hdi : s.gpr .rdi = L.base)
    (hfields : ∀ f, word s.mem L.base f.offset = L.fields f)
    (hps : Src s L.base usedBytes (L.fields .p) pb) (hqs : Src s L.base usedBytes (L.fields .q) qb)
    (hpl : pb.length = L.pLen) (hql : qb.length = L.qLen)
    (hpv : Spec.Dsa.decodeBE pb = L.modulus) (hqv : Spec.Dsa.decodeBE qb = L.subgroup)
    (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1) :
    WP isa SignVerify.workspaces s fun t => ∃ pmi qmi : BitVec 64,
      Ready { L with pInverse := pmi, qInverse := qmi } t ∧
      Outside L.base 48 (activeBytes - 48) s.mem t.mem ∧
      word t.mem L.base Field.mask.offset = word s.mem L.base Field.mask.offset ∧ Keep coreRegs s t := by
  have hpfield : word s.mem L.base Field.pLen.offset = BitVec.ofNat 64 pb.length := by
    rw [hpl]
    exact (hfields .pLen).trans L.pLength
  have hqfield : word s.mem L.base Field.qLen.offset = BitVec.ofNat 64 qb.length := by
    rw [hql]
    exact (hfields .qLen).trans L.qLength
  have hlens : Spec.Dsa.lengthsValid pb.length qb.length := by rw [hpl, hql]; exact L.lengths
  refine WP.mono (workspaces_ok hs hdi (by decide) (hfields .p) (hfields .q) hpfield hqfield
    hps hqs hlens (by rw [hpv]; exact hpo) (by rw [hqv]; exact hqo)) ?_
  intro t ⟨pmi, qmi, hg, hp, hq, hf, hk⟩
  simp only [hpl, hql, hpv, hqv] at hp hq hf
  have hsa : Scr t L.base activeBytes := by
    simpa only [off, BitVec.add_zero] using hg.scr.sub (o := 0) (n := activeBytes) (by decide) (by decide)
  refine ⟨pmi, qmi, ⟨⟨hsa, hg.rdi, hg.hdr⟩, hs.congr hk.2.2, ?_, hp, hq⟩,
    workspace_outside (L := L) hf, workspace_field hf .mask, hk⟩
  intro f _
  exact (workspace_field hf f).trans (hfields f)

end VG.Proof.Dsa.X86_64

end

end

/-! # Relating independently initialized workspaces without assuming scratch equality -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem ChildReady.inverse_unique {m₁ m₂ : Mem} {B : Addr} {o w n : Nat} {i₁ i₂ : BitVec 64}
    (h₁ : ChildReady m₁ B o w n i₁) (h₂ : ChildReady m₂ B o w n i₂)
    (hw : 1 ≤ w) (ho : n % 2 = 1) : i₁ = i₂ := by
  have e₁ : (word m₁ (off B o) (slot w aN)).toNat = n % 2 ^ 64 := by
    rw [← wv_mod64 _ _ _ hw, h₁.modulus]
  have e₂ : (word m₂ (off B o) (slot w aN)).toNat = n % 2 ^ 64 := by
    rw [← wv_mod64 _ _ _ hw, h₂.modulus]
  have i₁ := h₁.inverse
  have i₂ := h₂.inverse
  rw [e₁] at i₁
  rw [e₂] at i₂
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact ho) i₁ i₂

def ExecutionLayout.withInverses (L : ExecutionLayout) (pi qi : BitVec 64) : ExecutionLayout :=
  { L with pInverse := pi, qInverse := qi }

theorem readyInverses_eq {L : ExecutionLayout} {s₁ s₂ : State} {pi₁ qi₁ pi₂ qi₂ : BitVec 64}
    (h₁ : Ready (L.withInverses pi₁ qi₁) s₁) (h₂ : Ready (L.withInverses pi₂ qi₂) s₂)
    (hp : L.modulus % 2 = 1) (hq : L.subgroup % 2 = 1) : pi₁ = pi₂ ∧ qi₁ = qi₂ := by
  obtain ⟨hp2, _, hq2, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  exact ⟨h₁.pChild.inverse_unique h₂.pChild (by change 1 ≤ (L.pLen + 7) / 8; omega_using [hp2]) hp,
    h₁.qChild.inverse_unique h₂.qChild (by change 1 ≤ (L.qLen + 7) / 8; omega_using [hq2]) hq⟩

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
  rdi : s.gpr .rdi = p.layout.base
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
  · refine ⟨h.scratch, h.rdi, h.fields .p, h.fields .q, ?_, ?_, ?_, h.pSource, h.qSource⟩
    · change word s.mem p.layout.base Field.pLen.offset = BitVec.ofNat 64 p.pBytes.length
      rw [p.pLength]; exact (h.fields .pLen).trans p.layout.pLength
    · change word s.mem p.layout.base Field.qLen.offset = BitVec.ofNat 64 p.qBytes.length
      rw [p.qLength]; exact (h.fields .qLen).trans p.layout.qLength
    · change word s.mem p.layout.base Field.digestLen.offset = BitVec.ofNat 64 (p.layout.fields .digestLen).toNat
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.fields .digestLen
  · intro p s h
    exact WP.mono (workspacesReady_ok h.scratch h.rdi h.fields h.pSource h.qSource
      p.pLength p.qLength p.pValue p.qValue p.pOdd p.qOdd)
      fun t ⟨pi, qi, hr, _, hm, _⟩ => ⟨pi, qi, hr, hm.trans (h.fields .mask)⟩

theorem initialization_related {s₁ s₂ : State} (h : Two InitializationDone s₁ s₂) : Two Ready s₁ s₂ := by
  obtain ⟨p, ⟨pi₁, qi₁, h₁, _⟩, ⟨pi₂, qi₂, h₂, _⟩⟩ := h
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁ h₂ p.pOdd p.qOdd
  exact ⟨_, h₁, h₂⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Loading packed signing inputs into the verified arithmetic interface -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem Ready.inputOperand {L : ExecutionLayout} {s : State} (h : Ready L s)
    (f len : Field) (hf : f ≠ .mask) (hl : len ≠ .mask) {bs : List Byte}
    (hsrc : Src s L.base usedBytes (L.fields f) bs)
    (hlen : L.fields len = BitVec.ofNat 64 bs.length) :
    OperandBytes s L.base usedBytes ⟨.input f, len⟩ bs := by
  refine ⟨(h.fields len hl).trans hlen, ?_⟩
  simpa only [pointerValue, h.fields f hf] using hsrc

theorem signingOperands {p : SigningInput} {original s : State}
    {hp : original.gpr .r8 = BitVec.ofNat 64 p.pLen} {pi qi : BitVec 64}
    (h : Ready ((p.layout original hp).withInverses pi qi) s)
    (hkey : Src s p.base usedBytes (original.gpr .rdx) p.key)
    (hnonce : Src s p.base usedBytes (original.gpr .r9) p.nonce)
    (hdigest : Src s p.base usedBytes p.digestPointer p.digest) :
    SigningOperands ((p.layout original hp).withInverses pi qi) p.values p.components.y p.components.q s := by
  let L := (p.layout original hp).withInverses pi qi
  have hqlen : p.components.q.length = p.qLen := p.components.qLength
  have hglen : p.components.g.length = p.pLen := p.components.gLength
  have hylen : p.components.y.length = p.pLen := p.components.yLength
  have hxlen : p.components.x.length = p.qLen := component_length (by rw [p.keyLength]; omega_using [])
  have qptr : L.fields .q = original.gpr .rdx + BitVec.ofNat 64 p.pLen := by
    change original.gpr .rdx + original.gpr .r8 = _
    rw [hp]
  have gptr : L.fields .g = original.gpr .rdx + BitVec.ofNat 64 (p.pLen + p.qLen) := by
    change original.gpr .rdx + original.gpr .r8 + BitVec.ofNat 64 p.qLen = _
    rw [hp, Offset.add_add]
  have yptr : L.fields .y = original.gpr .rdx + BitVec.ofNat 64 (2 * p.pLen + p.qLen) := by
    change original.gpr .rdx + original.gpr .r8 + BitVec.ofNat 64 p.qLen + original.gpr .r8 = _
    rw [hp, Offset.add_add, Offset.add_add, show p.pLen + (p.qLen + p.pLen) = 2 * p.pLen + p.qLen by omega_using []]
  have xptr : L.fields .x = original.gpr .rdx + BitVec.ofNat 64 (3 * p.pLen + p.qLen) := by
    change original.gpr .rdx + original.gpr .r8 + BitVec.ofNat 64 p.qLen + original.gpr .r8 + original.gpr .r8 = _
    rw [hp, Offset.add_add, Offset.add_add, Offset.add_add,
      show p.pLen + (p.qLen + (p.pLen + p.pLen)) = 3 * p.pLen + p.qLen by omega_using []]
  have hqsrc : Src s p.base usedBytes (L.fields .q) p.components.q := by
    rw [qptr]; exact source_slice hkey (by rw [p.keyLength]; omega_using [])
  have hgsrc : Src s p.base usedBytes (L.fields .g) p.components.g := by
    rw [gptr]; exact source_slice hkey (by rw [p.keyLength]; omega_using [])
  have hysrc : Src s p.base usedBytes (L.fields .y) p.components.y := by
    rw [yptr]; exact source_slice hkey (by rw [p.keyLength]; omega_using [])
  have hxsrc : Src s p.base usedBytes (L.fields .x) p.components.x := by
    rw [xptr]; exact source_slice hkey (by rw [p.keyLength]; omega_using [])
  have hpfield : L.fields .pLen = BitVec.ofNat 64 p.pLen := hp
  have hqfield : L.fields .qLen = BitVec.ofNat 64 p.qLen := rfl
  refine ⟨h.inputOperand .g .pLen (by decide) (by decide) hgsrc (by change L.fields .pLen = BitVec.ofNat 64 p.components.g.length; rw [hglen]; exact hpfield),
    h.inputOperand .y .pLen (by decide) (by decide) hysrc (by rw [hylen]; exact hpfield),
    h.inputOperand .q .qLen (by decide) (by decide) hqsrc (by rw [hqlen]; exact hqfield),
    h.inputOperand .x .qLen (by decide) (by decide) hxsrc (by change L.fields .qLen = BitVec.ofNat 64 p.components.x.length; rw [hxlen]; exact hqfield),
    h.inputOperand .nonce .qLen (by decide) (by decide) hnonce (by change L.fields .qLen = BitVec.ofNat 64 p.nonce.length; rw [p.nonceLength]; exact hqfield),
    h.inputOperand .digest .digestPrefixLen (by decide) (by decide) (source_take hdigest) ?_,
    hglen, hylen, hqlen, hxlen, p.nonceLength, ?_, rfl⟩
  · change BitVec.ofNat 64 p.prefixLength = BitVec.ofNat 64 (p.digest.take _).length
    rw [List.length_take, Nat.min_comm]
  · change (p.digest.take _).length < 2 ^ 64
    simp only [List.length_take]
    exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) p.digestBound

end VG.Proof.Dsa.X86_64

end

end

/-! # Argument capture and public-domain validation for a complete signing attempt -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure SigningShapePost (p : SigningInput) (original : State)
    (hp : original.gpr .r8 = BitVec.ofNat 64 p.pLen) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  rdi : s.gpr .rdi = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp).fields f
  branch : s.zf = some (!p.accepted)
  saved : ∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)
  frame : InScr p.base usedBytes original.mem s.mem
  keep : Keep coreRegs original s

theorem shape_saved {s t : State} {B : Addr} (hf : Frm B shapeRanges s.mem t.mem) {i : Nat} (hi : i < 6) :
    word t.mem B (8 * i) = word s.mem B (8 * i) := by
  apply hf.word_eq _ (by omega_using [hi])
  intro range hr
  simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> left <;> omega_using [hi]

theorem signingShape_ok {p : SigningInput} {s0 : State} (h : SigningPre p s0) :
    WP isa (.seq (.block SignVerify.signEntry) Checks.domainShape) s0 (SigningShapePost p s0 h.pLength) := by
  refine WP.seq (WP.mono (signEntry_ok h.scratch rfl (by decide) h.stackRead h.stackSeparate
    h.qLength h.digestPointer h.digestLength h.base) fun s1 he => ?_)
  have hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  have hkey := h.keySource.congrK hinside he.keep
  have hps : Src s1 p.base usedBytes (s0.gpr .rdx) p.components.p := source_take hkey
  have hqs : Src s1 p.base usedBytes (s0.gpr .rdx + BitVec.ofNat 64 p.pLen) p.components.q :=
    source_slice hkey (by rw [p.keyLength]; omega_using [])
  have hp1 : 0 < p.components.p.length := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hq1 : 0 < p.components.q.length := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hp64 : p.components.p.length < 2 ^ 64 := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hq64 : p.components.q.length < 2 ^ 64 := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  refine WP.mono (domainShape_ok (h.scratch.congr he.keep.2.2) he.base (by decide) he.p
    (by rw [he.q, h.pLength]) (by rw [he.pLen, h.pLength, p.components.pLength])
    (by rw [he.qLen, p.components.qLength]) hps hqs hp1 hp64 hq1 hq64 rfl rfl
    p.digestBound he.digestLen) fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  have hall := he.keep.trans hk
  have hft : InScr p.base usedBytes s1.mem s2.mem := by
    apply InScr.of_frm hf
    intro range hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  exact ⟨h.scratch.congr hall.2.2, (hk.gpr (by decide)).trans he.base,
    he.shapeFields hf hprefix hmask, hbranch,
    fun i hi => (shape_saved hf hi).trans (he.saved i hi), hinside.trans hft,
    hall.mono (by decide)⟩

end VG.Proof.Dsa.X86_64
