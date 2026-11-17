module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningInput
public import VerifiedGarbage.Proof.Dsa.X86_64.SignBody
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.X86_64.WorkspacesCT
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
