module

public import VerifiedGarbage.Impl.Dsa.X86_64.Prevalidated
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyEntry
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingInitialize
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryFields
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.X86_64.KeygenEntry
import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.X86_64.SigningShape
import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
import VerifiedGarbage.Proof.Dsa.X86_64.PublicKey
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyFailure
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Functional correctness of the x86-64 DSA public-key validator

The entry stores verification's fields with no digest, so the verifier's
shape checks and workspaces apply unchanged; only the domain and public
value are then checked. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def validateFields : List Instr :=
  [.mov32 .rax (.imm 0), .store (SignVerify.initial .out) .rax, .store (SignVerify.initial .nonce) .rax,
    .store (SignVerify.initial .p) .rdi, .store (SignVerify.initial .pLen) .rdx,
    .store (SignVerify.initial .qLen) .rcx, .store (SignVerify.initial .signature) .r8,
    .store (SignVerify.initial .digest) .rax, .store (SignVerify.initial .digestLen) .rax]

theorem validateFields_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block validateFields) s fun t =>
      t.mem = verifyFieldMem s.mem B (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) 0 0 ∧
      Keep [.rax] s t := by
  refine WP.keep [.rax] ?_ rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold validateFields
  xrun [State.ea, SignVerify.initial, h11, fieldAddress,
    hw .out, hw .nonce, hw .p, hw .pLen, hw .qLen, hw .signature, hw .digest, hw .digestLen]
  rfl

theorem validateEntry_ok {s0 : State} {B digest digestLen : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (h8 : s0.gpr .r8 = B) (hZ : pWorkspace ≤ Z)
    (hd : digest = 0) (hdl : digestLen = 0) :
    WP isa (.block Prevalidated.validateEntry) s0 (VerifyEntryPost s0 B digest digestLen) := by
  subst hd hdl
  change WP isa (.block (([.mov .r11 (.reg .r8)] : List Instr) ++ SignVerify.save ++ validateFields ++
    SignVerify.keyPointers)) s0 _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (moveScratch_ok s0) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [h8] at h11
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (hs.congr hk1.2.2) h11 (Nat.le_trans (by decide) hZ)) fun s2 ⟨hsaved, hf2, hk2⟩ => ?_
  have hk12 := hk1.trans hk2
  have hreg (reg : Reg) (hne : reg ≠ .r11) : s2.gpr reg = s0.gpr reg := hk12.gpr (by simpa using hne)
  rw [WP.block_append_iff]
  refine WP.mono (validateFields_ok (hs.congr hk12.2.2) ((hk2.gpr (by decide)).trans h11) hZ)
    fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .rdi (by decide), hreg .rdx (by decide), hreg .rcx (by decide), hreg .r8 (by decide)] at hmem3
  have hfields := verifyFieldMem_fields s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx) (s0.gpr .r8) 0 0
  rw [← hmem3] at hfields
  have hunused := verifyFieldMem_unused s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx) (s0.gpr .r8) 0 0
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s2.mem s3.mem := by rw [hmem3]; exact verifyFieldMem_frame _ _ _ _ _ _ _ _
  have hk123 := hk12.trans hk3
  have h113 : s3.gpr .r11 = B := (hk3.gpr (by decide)).trans ((hk2.gpr (by decide)).trans h11)
  refine WP.mono (keyPointers_ok (hs.congr hk123.2.2) h113 hZ hfields.1 hfields.2.1 hfields.2.2.1)
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hptr := keyPointerMem_fields s3.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx)
  rw [← hmem4] at hptr
  have hf4 : Outside B 264 32 s3.mem s4.mem := by rw [hmem4]; exact keyPointerMem_frame _ _ _ _ _
  have hsame (f : Field) (hsep : f.offset + 8 ≤ 264 ∨ 296 ≤ f.offset) :
      word s4.mem B f.offset = word s3.mem B f.offset :=
    hf4.word hsep (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  refine ⟨hdi4, (hsame .p (by decide)).trans hfields.1, (hsame .pLen (by decide)).trans hfields.2.1,
    (hsame .qLen (by decide)).trans hfields.2.2.1, (hsame .signature (by decide)).trans hfields.2.2.2.1,
    (hsame .digest (by decide)).trans hfields.2.2.2.2.1, (hsame .digestLen (by decide)).trans hfields.2.2.2.2.2,
    hptr.1, hptr.2.1, hptr.2.2.1, hptr.2.2.2, ?_, ?_, ?_, (hk123.trans hk4).mono (by decide)⟩
  · exact ⟨(hsame .out (by decide)).trans hunused.1, (hsame .nonce (by decide)).trans hunused.2⟩
  · intro i hi
    exact ((hf4.word (Or.inl (by omega)) (by omega)).trans (entry_saved_frame hf3 hi)).trans
      ((hsaved i hi).trans (hk1.gpr (by simpa using saved_ne_r11 hi)))
  · have hwide2 : Outside B 0 pWorkspace s0.mem s2.mem := by
      rw [← hmem1]
      exact hf2.mono (Nat.le_refl _) (by decide)
    exact (hwide2.trans (hf3.mono (by decide) (by decide))).trans (hf4.mono (by decide) (by decide))

structure ValidatingPre (p : VerifyingInput) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  pLength : s.gpr .rdx = BitVec.ofNat 64 p.pLen
  qLength : s.gpr .rcx = BitVec.ofNat 64 p.qLen
  base : s.gpr .r8 = p.base
  keySource : Src s p.base usedBytes (s.gpr .rdi) p.key
  digestNil : p.digest = []
  digestPointer : p.digestPointer = 0

theorem validatingShape_ok {p : VerifyingInput} {s0 : State} (h : ValidatingPre p s0) :
    WP isa (.seq (.block Prevalidated.validateEntry) Checks.domainShape) s0
      (VerifyingShapePost p s0 h.pLength h.qLength) := by
  refine WP.seq (WP.mono (validateEntry_ok (digest := p.digestPointer)
    (digestLen := BitVec.ofNat 64 p.digest.length) h.scratch h.base (by decide) h.digestPointer
    (by rw [h.digestNil]; rfl)) fun s1 he => ?_)
  have hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  have hkey := h.keySource.congrK hinside he.keep
  have hps : Src s1 p.base usedBytes (s0.gpr .rdi) p.components.p := source_take hkey
  have hqs : Src s1 p.base usedBytes (s0.gpr .rdi + BitVec.ofNat 64 p.pLen) p.components.q :=
    source_slice hkey (by rw [p.keyLength]; omega)
  have hp1 : 0 < p.components.p.length := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hq1 : 0 < p.components.q.length := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hp64 : p.components.p.length < 2 ^ 64 := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hq64 : p.components.q.length < 2 ^ 64 := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  refine WP.mono (domainShape_ok (h.scratch.congr he.keep.2.2) he.base (by decide) he.p
    (by rw [he.q, h.pLength]) (by rw [he.pLen, h.pLength, p.components.pLength])
    (by rw [he.qLen, h.qLength, p.components.qLength]) hps hqs hp1 hp64 hq1 hq64 rfl rfl
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

theorem validatingOperands {p : VerifyingInput} {original s : State}
    {hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen}
    {hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen} {pi qi : BitVec 64}
    (h : Ready ((p.layout original hp hq).withInverses pi qi) s)
    (hkey : Src s p.base usedBytes (original.gpr .rdi) p.key) :
    OperandBytes s p.base usedBytes Core.generator p.components.g ∧
    OperandBytes s p.base usedBytes Core.publicValue p.components.y ∧
    OperandBytes s p.base usedBytes ⟨.input .q, .qLen⟩ p.components.q := by
  let L := (p.layout original hp hq).withInverses pi qi
  have hqlen : p.components.q.length = p.qLen := p.components.qLength
  have hglen : p.components.g.length = p.pLen := p.components.gLength
  have hylen : p.components.y.length = p.pLen := p.components.yLength
  have qptr : L.fields .q = original.gpr .rdi + BitVec.ofNat 64 p.pLen := by
    change original.gpr .rdi + original.gpr .rdx = _
    rw [hp]
  have gptr : L.fields .g = original.gpr .rdi + BitVec.ofNat 64 (p.pLen + p.qLen) := by
    change original.gpr .rdi + original.gpr .rdx + original.gpr .rcx = _
    rw [hp, hq, Offset.add_add]
  have yptr : L.fields .y = original.gpr .rdi + BitVec.ofNat 64 (2 * p.pLen + p.qLen) := by
    change original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx = _
    rw [hp, hq, Offset.add_add, Offset.add_add, show p.pLen + (p.qLen + p.pLen) = 2 * p.pLen + p.qLen by omega]
  have hqsrc : Src s p.base usedBytes (L.fields .q) p.components.q := by
    rw [qptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hgsrc : Src s p.base usedBytes (L.fields .g) p.components.g := by
    rw [gptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hysrc : Src s p.base usedBytes (L.fields .y) p.components.y := by
    rw [yptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hpfield : L.fields .pLen = BitVec.ofNat 64 p.pLen := hp
  have hqfield : L.fields .qLen = BitVec.ofNat 64 p.qLen := hq
  exact ⟨h.inputOperand .g .pLen (by decide) (by decide) hgsrc
      (by change L.fields .pLen = BitVec.ofNat 64 p.components.g.length; rw [hglen]; exact hpfield),
    h.inputOperand .y .pLen (by decide) (by decide) hysrc
      (by change L.fields .pLen = BitVec.ofNat 64 p.components.y.length; rw [hylen]; exact hpfield),
    h.inputOperand .q .qLen (by decide) (by decide) hqsrc (by rw [hqlen]; exact hqfield)⟩

def ValidatingInitialized (p : VerifyingInput) (original : State)
    (hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp hq).withInverses pi qi) s ∧
    (OperandBytes s p.base usedBytes Core.generator p.components.g ∧
      OperandBytes s p.base usedBytes Core.publicValue p.components.y ∧
      OperandBytes s p.base usedBytes ⟨.input .q, .qLen⟩ p.components.q) ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    (∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)) ∧
    InScr p.base usedBytes original.mem s.mem ∧ Keep coreRegs original s

theorem validatingInitialize_ok {p : VerifyingInput} {original s : State} (h : ValidatingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces s (ValidatingInitialized p original h.pLength h.qLength) := by
  let L := p.layout original h.pLength h.qLength
  have hkey := h.keySource.congrK hs.frame hs.keep
  have hps : Src s L.base usedBytes (L.fields .p) p.components.p := source_take hkey
  have hqs : Src s L.base usedBytes (L.fields .q) p.components.q := by
    change Src s p.base usedBytes (original.gpr .rdi + original.gpr .rdx) p.components.q
    rw [h.pLength]
    exact source_slice hkey (by rw [p.keyLength]; omega)
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  refine WP.mono (workspacesReady_ok (L := L) hs.scratch hs.rdi hs.fields hps hqs p.components.pLength
    p.components.qLength rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  have hframe : InScr p.base usedBytes s.mem t.mem := InScr.of_outside hf (by decide)
  have hfull := hs.frame.trans hframe
  have hkeep := hs.keep.trans hk
  refine ⟨pi, qi, hr, validatingOperands hr (h.keySource.congrK hfull hkeep), ?_, ?_, hfull,
    hkeep.mono (by decide)⟩
  · exact hm.trans ((hs.fields .mask).trans (congrArg mask ha))
  · intro i hi
    exact (hf.word (Or.inl (by omega)) (by omega)).trans (hs.saved i hi)

def ValidatingPost (p : VerifyingInput) (original t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key).toNat ∧
  (∀ i < 6, t.gpr (saved.getD i .rax) = original.gpr (saved.getD i .rax)) ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem validatingBody_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {original s : State}
    (h : ValidatingPre p original)
    (hi : ValidatingInitialized p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa (seqs [Checks.publicKey Sq.mm M.mm, .block SignVerify.result]) s (ValidatingPost p original) := by
  obtain ⟨pi, qi, hr, ⟨hg, hy, hqb⟩, hm, hsave, hf, hk⟩ := hi
  let L := (p.layout original h.pLength h.qLength).withInverses pi qi
  obtain ⟨hsize, hpodd, hqodd⟩ := p.shapeFacts ha
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hpf : L.modulus ≤ 256 ^ L.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.p
    rw [p.components.pLength] at hh
    exact Nat.le_of_lt hh
  have hqf : L.subgroup ≤ 256 ^ L.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.q
    rw [p.components.qLength] at hh
    exact Nat.le_of_lt hh
  have he : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key =
      publicAccepted L p.components.g p.components.y true := by
    rw [publicAccepted_spec L p.components.g p.components.y hsize hpodd hqodd]
    simp only [Spec.Dsa.validatePublicKeyBytes, p.lengths, decide_true, Bool.not_true,
      p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rfl
  refine WP.seq (WP.mono (publicKey_ok M Sq hr hp hq hpodd hqodd hpf hqf hg hy hqb
    p.components.gLength p.components.yLength p.components.qLength rfl hm)
    fun t ⟨ht, hmask, _, hframe, hkeep⟩ => ?_)
  refine WP.mono (result_ok ht.scratch ht.parent.rdi (by decide) hmask) fun u ⟨hret, hsaved, hmem, hku⟩ => ?_
  refine ⟨?_, fun i hi => ?_, ?_, ((hk.trans hkeep).trans hku).mono (by decide)⟩
  · rw [he]; exact hret
  · exact ((hsaved i hi).trans (hframe.word (Or.inl (by omega)) (by omega))).trans (hsave i hi)
  · rw [hmem]
    exact hf.trans (InScr.of_outside hframe (by decide))

theorem validatingMain_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {s0 : State} (h : ValidatingPre p s0) :
    WP isa (Prevalidated.validate Sq.mm M.mm) s0 (ValidatingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (validatingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · change eval .e s = some true
      simp only [eval, hs.branch, ha, Bool.not_false]
    · have hp := shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
      change ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes p.pLen p.qLen p.key).params at hp
      have hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = false := by
        simp only [Spec.Dsa.validatePublicKeyBytes, p.lengths, decide_true, Bool.not_true,
          p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        simp only [hp, decide_false, Bool.false_and]
      refine WP.mono (verifyFailure_ok hs.scratch hs.rdi (by decide))
        fun t ⟨hret, hsave, hmem, hk⟩ => ?_
      exact ⟨by rw [hv]; exact hret, fun i hi => (hsave i hi).trans (hs.saved i hi),
        by rw [hmem]; exact hs.frame, (hs.keep.trans hk).mono (by decide)⟩
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change eval .e s = some false
      simp only [eval, hs.branch, ha, Bool.not_true]
    · refine WP.seq (WP.mono (validatingInitialize_ok h hs ha) fun t ht => ?_)
      exact validatingBody_ok M Sq h ht ha

end VG.Proof.Dsa.X86_64
