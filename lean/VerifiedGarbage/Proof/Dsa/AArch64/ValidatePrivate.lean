module

public import VerifiedGarbage.Proof.Dsa.AArch64.KeygenEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningKey
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSpec
public import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
public import VerifiedGarbage.Proof.Dsa.AArch64.CoreSign
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
public import VerifiedGarbage.Proof.Dsa.AArch64.SignCompute
public import VerifiedGarbage.Impl.Dsa.AArch64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
import VerifiedGarbage.Proof.Dsa.AArch64.PrivateKey
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Functional correctness of the AArch64 DSA private-key validator

The validator is the signer's checks of the key (`Checks.signingKey` and
`Checks.privateKey`) after the domain check's register entry, with the
nonce field pointing at x: its range check is then x's, which the key's
consistency already includes. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def privateFieldValues (original : State) (valid : Bool) : Field → Addr
  | .p => original.gpr .x0
  | .q => original.gpr .x0 + original.gpr .x2
  | .g => original.gpr .x0 + original.gpr .x2 + original.gpr .x3
  | .y => original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2
  | .x => original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2 + original.gpr .x2
  | .signature => 0
  | .nonce => original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2 + original.gpr .x2
  | .digest => 0
  | .out => 0
  | .pLen => original.gpr .x2
  | .qLen => original.gpr .x3
  | .digestLen => 0
  | .digestPrefixLen => 0
  | .mask => mask valid

/-- Point the nonce at x. -/
theorem nonceScalar_ok {s : State} {B v : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z)
    (hx : word s.mem B Field.x.offset = v) :
    WP isa (.block [.ldr .x .x3 .x11 Field.x.offset, SignVerify.initial .x3 .nonce]) s fun t =>
      t.mem = s.mem.writeW (off B Field.nonce.offset) v ∧ Keep [.x3] s t := by
  refine WP.keep [.x3] ?_ rfl rfl rfl
  have hl (f : Field) := hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  brun [SignVerify.initial, h11, fieldAddress, field_enc .x, field_enc .nonce, hl .x, hw .nonce, hx]

theorem privateEntry_ok {s0 : State} {B : Addr} (hs : Scr s0 B usedBytes) (h8 : s0.gpr .x4 = B) :
    WP isa (.block PrevalidatedSign.validateEntry) s0 (KeygenEntryPost s0 B (privateFieldValues s0 true)) := by
  unfold PrevalidatedSign.validateEntry
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (moveScratch_ok s0) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [h8] at h11
  rw [WP.block_append_iff]
  have hreg (reg : Reg) (hne : reg ≠ .x11) : s1.gpr reg = s0.gpr reg := hk1.gpr reg (by simpa using hne)
  refine WP.mono (checkFields_ok (hs.congr hk1.wr) h11 (by decide)) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .x0 (by decide), hreg .x2 (by decide), hreg .x3 (by decide)] at hmem3
  have hk123 := hk1.trans hk3
  have h113 : s3.gpr .x11 = B := (hk3.gpr .x11 (by decide)).trans h11
  have hw3 (f : Field) : word s3.mem B f.offset =
      word (checkFieldMem s1.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3)) B f.offset := by rw [hmem3]
  rw [WP.block_append_iff]
  refine WP.mono (keyPointers_ok (p := s0.gpr .x0) (pl := s0.gpr .x2) (ql := s0.gpr .x3) (hs.congr hk123.wr) h113 (by decide)
    ((hw3 .p).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl))
    ((hw3 .pLen).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl))
    ((hw3 .qLen).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl)))
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hk1234 := hk123.trans hk4
  have h114 : s4.gpr .x11 = B := (hk4.gpr .x11 (by decide)).trans h113
  have hx4 : word s4.mem B Field.x.offset =
      s0.gpr .x0 + s0.gpr .x2 + s0.gpr .x3 + s0.gpr .x2 + s0.gpr .x2 := by
    rw [hmem4]; exact (keyPointerMem_fields _ _ _ _ _).2.2.2
  refine WP.mono (nonceScalar_ok (hs.congr hk1234.wr) h114 (by decide) hx4) fun t ⟨hmem5, hk5⟩ => ?_
  refine ⟨(hk5.gpr .x0 (by decide)).trans hdi4, ?_, ?_,
    ((hk1234.trans hk5).mono (by decide))⟩
  · intro f h1 h2
    rw [hmem5, hmem4, hmem3]
    cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 |
      (simp only [checkFieldMem, keyPointerMem, word_fieldWrite, reduceCtorEq, reduceIte, privateFieldValues]; try rfl)
  · intro x hx
    have hx' : ofs B x < 256 ∨ pWorkspace ≤ ofs B x := by omega
    rw [hmem5, hmem4, hmem3]
    simp only [checkFieldMem, keyPointerMem, field_write_frame _ B _ _ x hx']
    rw [hmem1]

structure PrivateInput where
  base : Addr
  pLen : Nat
  qLen : Nat
  key : List Byte
  lengths : Spec.Dsa.lengthsValid pLen qLen
  keyLength : key.length = 3 * pLen + 2 * qLen

namespace PrivateInput

variable (p : PrivateInput)

def components : PackedComponents p.pLen p.qLen :=
  packedComponents p.pLen p.qLen p.key (by rw [p.keyLength]; omega)

theorem xLength : p.components.x.length = p.qLen := component_length (by rw [p.keyLength]; omega)

theorem pPositive : 0 < p.components.p.length := by
  rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
theorem qPositive : 0 < p.components.q.length := by
  rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega

abbrev accepted : Bool := shapeAccepted p.components.p p.components.q p.pPositive p.qPositive

theorem shapeFacts {p : PrivateInput} (ha : p.accepted = true) :
    Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.components.p))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.components.q)) ∧
    Spec.Dsa.decodeBE p.components.p % 2 = 1 ∧ Spec.Dsa.decodeBE p.components.q % 2 = 1 := by
  rw [PrivateInput.accepted, shapeAccepted_spec] at ha
  exact of_decide_eq_true ha

def layout (original : State) (hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen) : ExecutionLayout where
  base := p.base
  pLen := p.pLen
  qLen := p.qLen
  modulus := Spec.Dsa.decodeBE p.components.p
  subgroup := Spec.Dsa.decodeBE p.components.q
  pInverse := 0
  qInverse := 0
  fields := privateFieldValues original p.accepted
  lengths := p.lengths
  pLength := hp
  qLength := hq

/-- The signer's values for the key's checks: the nonce is x. -/
def values : SignValues := ⟨p.components.g, p.components.x, p.components.x, []⟩

end PrivateInput

structure PrivatePre (p : PrivateInput) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  base : s.gpr .x4 = p.base
  pLength : s.gpr .x2 = BitVec.ofNat 64 p.pLen
  qLength : s.gpr .x3 = BitVec.ofNat 64 p.qLen
  keySource : Src s p.base usedBytes (s.gpr .x0) p.key

theorem PrivatePre.sources {p : PrivateInput} {original s : State} (h : PrivatePre p original)
    (hm : InScr p.base usedBytes original.mem s.mem) (hk : Keep coreRegs original s) :
    Src s p.base usedBytes (original.gpr .x0) p.components.p ∧
    Src s p.base usedBytes (original.gpr .x0 + original.gpr .x2) p.components.q ∧
    Src s p.base usedBytes (original.gpr .x0 + original.gpr .x2 + original.gpr .x3) p.components.g ∧
    Src s p.base usedBytes (original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2)
      p.components.y ∧
    Src s p.base usedBytes (original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2 +
      original.gpr .x2) p.components.x := by
  have hsrc := h.keySource.congrK hm hk
  refine ⟨source_take hsrc, ?_, ?_, ?_, ?_⟩
  · rw [h.pLength]
    exact source_slice hsrc (by rw [p.keyLength]; omega)
  · rw [h.pLength, h.qLength, Offset.add_add]
    exact source_slice hsrc (by rw [p.keyLength]; omega)
  · rw [h.pLength, h.qLength, Offset.add_add, Offset.add_add,
      show p.pLen + (p.qLen + p.pLen) = 2 * p.pLen + p.qLen by omega]
    exact source_slice hsrc (by rw [p.keyLength]; omega)
  · rw [h.pLength, h.qLength, Offset.add_add, Offset.add_add, Offset.add_add,
      show p.pLen + (p.qLen + (p.pLen + p.pLen)) = 3 * p.pLen + p.qLen by omega]
    exact source_slice hsrc (by rw [p.keyLength]; omega)

structure PrivateShapePost (p : PrivateInput) (original : State)
    (hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  x0 : s.gpr .x0 = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp hq).fields f
  branch : (s.gpr .x3 == (0#64)) = !p.accepted
  frame : InScr p.base usedBytes original.mem s.mem
  keep : Keep coreRegs original s

theorem privateShape_ok {p : PrivateInput} {s0 : State} (h : PrivatePre p s0) :
    WP isa (.seq (.block PrevalidatedSign.validateEntry) Checks.domainShape) s0
      (PrivateShapePost p s0 h.pLength h.qLength) := by
  refine WP.seq (WP.mono (privateEntry_ok h.scratch h.base) fun s1 he => ?_)
  have hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _⟩ := h.sources hinside (he.keep.mono (by decide))
  have hp64 : p.components.p.length < 2 ^ 64 := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hq64 : p.components.q.length < 2 ^ 64 := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  refine WP.mono (domainShape_ok (h.scratch.congr he.keep.wr) he.base (by decide)
    (he.fields .p (by decide) (by decide)) (he.fields .q (by decide) (by decide))
    ((he.fields .pLen (by decide) (by decide)).trans (by rw [p.components.pLength]; exact h.pLength))
    ((he.fields .qLen (by decide) (by decide)).trans (by rw [p.components.qLength]; exact h.qLength))
    hps hqs p.pPositive hp64 p.qPositive hq64 rfl rfl (by decide)
    (he.fields .digestLen (by decide) (by decide))) fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  have hall := he.keep.trans hk
  have hft : InScr p.base usedBytes s1.mem s2.mem := by
    apply InScr.of_frm hf
    intro range hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  refine ⟨h.scratch.congr hall.wr, (hk.gpr .x0 (by decide)).trans he.base,
    he.shapeFields hf ?_ (by rw [hprefix]; rfl) hmask, hbranch,
    hinside.trans hft, hall.mono (by decide)⟩
  intro f h1 h2
  cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 | rfl

def PrivatePost (p : PrivateInput) (original t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 (if Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key then 1 else 0) ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem privateRejected_ok {p : PrivateInput} {original s : State} (h : PrivatePre p original)
    (hs : PrivateShapePost p original h.pLength h.qLength s) (ha : p.accepted = false) :
    WP isa (.block [movi .x0 0]) s (PrivatePost p original) := by
  have hp := shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
  change ¬ Spec.Dsa.parametersValid (Spec.Dsa.privateKeyBytes p.pLen p.qLen p.key).params at hp
  have hv : Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key = false := by
    simp only [Spec.Dsa.validatePrivateKeyBytes, p.lengths, decide_true, Bool.not_true,
      p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    simp only [hp, decide_false, Bool.false_and]
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨hret, hmem⟩, hk⟩ => ?_
  unfold PrivatePost
  rw [hv]
  exact ⟨hret, by rw [hmem]; exact hs.frame, (hs.keep.trans hk).mono (by decide)⟩

/-- After the workspaces: the key's operands, with x as the nonce. -/
structure PrivateOperands (L : ExecutionLayout) (p : PrivateInput) (s : State) : Prop where
  generator : OperandBytes s L.base usedBytes Core.generator p.components.g
  publicValue : OperandBytes s L.base usedBytes Core.publicValue p.components.y
  subgroup : OperandBytes s L.base usedBytes ⟨.input .q, .qLen⟩ p.components.q
  privateScalar : OperandBytes s L.base usedBytes Core.privateScalar p.components.x
  nonce : OperandBytes s L.base usedBytes Core.nonce p.components.x

def PrivateInitialized (p : PrivateInput) (original : State)
    (hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp hq).withInverses pi qi) s ∧
    PrivateOperands ((p.layout original hp hq).withInverses pi qi) p s ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    InScr p.base usedBytes original.mem s.mem ∧ Keep coreRegs original s

theorem privateInitialize_ok {p : PrivateInput} {original st : State} (h : PrivatePre p original)
    (hs : PrivateShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces st (PrivateInitialized p original h.pLength h.qLength) := by
  let L := p.layout original h.pLength h.qLength
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hps, hqs, _⟩ := h.sources hs.frame hs.keep
  refine WP.mono (workspacesReady_ok (L := L) hs.scratch hs.x0 hs.fields hps hqs
    p.components.pLength p.components.qLength rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  let L' := L.withInverses pi qi
  have hr' : Ready L' t := hr
  have hframe : InScr p.base usedBytes original.mem t.mem :=
    hs.frame.trans (InScr.of_outside hf (by decide))
  have hkeep := hs.keep.trans hk
  obtain ⟨_, hqs', hgs', hys', hxs'⟩ := h.sources hframe (hkeep.mono (by decide))
  have hpl (bs : List Byte) (hb : bs.length = p.pLen) : L'.fields .pLen = BitVec.ofNat 64 bs.length := by
    rw [hb]; exact h.pLength
  have hql (bs : List Byte) (hb : bs.length = p.qLen) : L'.fields .qLen = BitVec.ofNat 64 bs.length := by
    rw [hb]; exact h.qLength
  refine ⟨pi, qi, hr', ⟨hr'.inputOperand .g .pLen (by decide) (by decide) hgs' (hpl _ p.components.gLength),
    hr'.inputOperand .y .pLen (by decide) (by decide) hys' (hpl _ p.components.yLength),
    hr'.inputOperand .q .qLen (by decide) (by decide) hqs' (hql _ p.components.qLength),
    hr'.inputOperand .x .qLen (by decide) (by decide) hxs' (hql _ p.xLength),
    hr'.inputOperand .nonce .qLen (by decide) (by decide) hxs' (hql _ p.xLength)⟩,
    hm.trans ((hs.fields .mask).trans (congrArg mask ha)),
    hframe, hkeep.mono (by decide)⟩

theorem and_redundant {a b c : Bool} (h : b = true → c = true) : (a && b && c) = (a && b) := by
  cases a <;> cases b <;> simp_all

/-- With x as the nonce, the signer's acceptance of the key is its validation:
the nonce's range check is x's, which `keyValid` already includes. -/
theorem PrivateInput.validate_eq (p : PrivateInput) {pi qi : BitVec 64} {original : State}
    {hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen} {hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen}
    (ha : p.accepted = true) :
    privateAccepted ((p.layout original hp hq).withInverses pi qi) p.values p.components.y true =
      Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key := by
  let L := (p.layout original hp hq).withInverses pi qi
  obtain ⟨hsize, hpodd, hqodd⟩ := p.shapeFacts ha
  have hpf : L.modulus ≤ 256 ^ L.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.p
    rw [p.components.pLength] at hh
    exact Nat.le_of_lt hh
  rw [privateAccepted_spec L p.values p.components.y hsize hpodd hqodd hpf p.components.yLength,
    and_redundant (fun hkv => ?_)]
  · simp only [Spec.Dsa.validatePrivateKeyBytes, p.lengths, decide_true, Bool.not_true,
      p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only [Spec.Dsa.keyValid, Bool.and_eq_true, decide_eq_true_eq] at hkv
    exact decide_eq_true ⟨hkv.2.1.1, hkv.2.1.2⟩

theorem privateSuccess_ok (M : Mont) {p : PrivateInput} {original st : State}
    (h : PrivatePre p original)
    (hs : PrivateShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.signingKey M.mm, Checks.privateKey M.mm,
      .block SignVerify.result]) st (PrivatePost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  refine WP.seq (WP.mono (privateInitialize_ok h hs ha) fun t ⟨pi, qi, hr, ho, hm, hframe, hkeep⟩ => ?_)
  let L := (p.layout original h.pLength h.qLength).withInverses pi qi
  have hpf : L.modulus ≤ 256 ^ L.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.p; rw [p.components.pLength] at hh; exact Nat.le_of_lt hh
  have hqf : L.subgroup ≤ 256 ^ L.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.q; rw [p.components.qLength] at hh; exact Nat.le_of_lt hh
  refine WP.seq (WP.mono (signingKey_ok M hr hp1 hq255 hpo hqo hpf hqf ho.generator ho.publicValue
    ho.subgroup p.components.gLength p.components.yLength p.components.qLength rfl hm)
    fun u ⟨hu, hmu, _, hfu, hku⟩ => ?_)
  have hg1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.generator]) ho.generator
  have hy1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.publicValue]) ho.publicValue
  have hx1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.privateScalar]) ho.privateScalar
  have hn1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.nonce]) ho.nonce
  refine WP.seq (WP.mono (privateKey_ok M hu hp1 hpo hg1 hy1 hx1 hn1 p.components.gLength
    p.components.yLength p.xLength p.xLength hmu) fun w ⟨hw, hmw, _, hfw, hkw⟩ => ?_)
  have hmv : word w.mem L.base Field.mask.offset =
      mask (Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key) :=
    hmw.trans (congrArg mask ((privateAccepted_signingKey L p.values p.components.y true hp1 hpf).trans
      (p.validate_eq ha)))
  refine WP.mono (result_ok hw.scratch hw.parent.x0 (by decide) hmv) fun v ⟨hret, hmem, hkv⟩ => ?_
  refine ⟨?_, ?_, (((hkeep.trans hku).trans hkw).trans hkv).mono (by decide)⟩
  · rw [hret]; exact toNat_ofNat_if _
  · rw [hmem]; exact hframe.trans (InScr.of_outside (hfu.trans hfw) (by decide))

theorem privateMain_ok (M : Mont) {p : PrivateInput} {s0 : State} (h : PrivatePre p s0) :
    WP isa (PrevalidatedSign.validate M.mm) s0 (PrivatePost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (privateShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => privateRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    rw [hs.branch, ha]; rfl
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => privateSuccess_ok M h hs ha)
    change some (s.gpr .x3 == (0#64)) = some false
    rw [hs.branch, ha]; rfl

end VG.Proof.Dsa.AArch64
