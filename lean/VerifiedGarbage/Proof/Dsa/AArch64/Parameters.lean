module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyCompute
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSpec
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
public import VerifiedGarbage.Spec.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.AArch64.Generate
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.Operands

/-! ### `Dsa.AArch64.KeygenEntry`, which this module and modules that import it used -/

section

/-! # AAPCS64 entry of the domain check and key derivation

Both entries save the callee-saved registers and fill every field but the
digest prefix and the mask, which the shape checks write. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem word_fieldWrite (mem : Mem) (B : Addr) (v : BitVec 64) (f r : Field) :
    word (mem.writeW (off B f.offset) v) B r.offset = if f = r then v else word mem B r.offset := by
  by_cases h : f = r
  · subst h
    simp [word_writeW_self]
  · simp only [h, ↓reduceIte]
    exact field_write_other _ _ _ _ _ h

/-- Fields captured by the caller-saved-register entry. -/
structure KeygenEntryPost (original : State) (B : Addr) (values : Field → Addr) (t : State) : Prop where
  base : t.gpr .x0 = B
  fields : ∀ f, f ≠ .digestPrefixLen → f ≠ .mask → word t.mem B f.offset = values f
  frame : Outside B 0 pWorkspace original.mem t.mem
  keep : Keep [.x0, .x3, .x11, .x12, .x13] original t

def checkFieldValues (original : State) (valid : Bool) : Field → Addr
  | .p => original.gpr .x0
  | .q => original.gpr .x0 + original.gpr .x2
  | .g => original.gpr .x0 + original.gpr .x2 + original.gpr .x3
  | .y => original.gpr .x0 + original.gpr .x2 + original.gpr .x3
  | .x => original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2 + original.gpr .x2
  | .signature => 0
  | .nonce => 0
  | .digest => 0
  | .out => 0
  | .pLen => original.gpr .x2
  | .qLen => original.gpr .x3
  | .digestLen => 0
  | .digestPrefixLen => 0
  | .mask => mask valid

abbrev checkFields := Generate.checkFields

def checkFieldMem (mem : Mem) (B p pl ql : Addr) : Mem :=
  ((((((((mem.writeW (off B Field.signature.offset) (0#64)).writeW (off B Field.out.offset) (0#64)).writeW
    (off B Field.nonce.offset) (0#64)).writeW (off B Field.digest.offset) (0#64)).writeW
    (off B Field.digestLen.offset) (0#64)).writeW (off B Field.p.offset) p).writeW
    (off B Field.pLen.offset) pl).writeW (off B Field.qLen.offset) ql)

theorem checkFields_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block checkFields) s fun t =>
      t.mem = checkFieldMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) ∧ Keep [.x12] s t := by
  refine WP.keep [.x12] ?_ rfl rfl rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold checkFields Generate.checkFields
  brun [SignVerify.initial, h11, fieldAddress,
    field_enc .signature, field_enc .out, field_enc .nonce, field_enc .digest,
    field_enc .digestLen, field_enc .p, field_enc .pLen, field_enc .qLen,
    hw .signature, hw .out, hw .nonce, hw .digest, hw .digestLen, hw .p, hw .pLen, hw .qLen]
  rfl

/-- Point the public value at g. -/
theorem publicGenerator_ok {s : State} {B v : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z)
    (hg : word s.mem B Field.g.offset = v) :
    WP isa (.block [.ldr .x .x3 .x11 Field.g.offset, SignVerify.initial .x3 .y]) s fun t =>
      t.mem = s.mem.writeW (off B Field.y.offset) v ∧ Keep [.x3] s t := by
  refine WP.keep [.x3] ?_ rfl rfl rfl
  have hl (f : Field) := hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  brun [SignVerify.initial, h11, fieldAddress, field_enc .g, field_enc .y, hl .g, hw .y, hg]

theorem moveScratch_ok (s : State) :
    WP isa (.block [mov .x11 .x4]) s fun t =>
      t.gpr .x11 = s.gpr .x4 ∧ t.mem = s.mem ∧ Keep [.x11] s t := by
  refine WP.mono (WP.keep [.x11] (Q := fun t => t.gpr .x11 = s.gpr .x4 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hp, hm⟩, hk⟩ => ⟨hp, hm, hk⟩
  brun []

theorem checkEntry_ok {s0 : State} {B : Addr} (hs : Scr s0 B usedBytes) (h8 : s0.gpr .x4 = B) :
    WP isa (.block Generate.checkEntry) s0 (KeygenEntryPost s0 B (checkFieldValues s0 true)) := by
  unfold Generate.checkEntry
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
  have hg4 : word s4.mem B Field.g.offset = s0.gpr .x0 + s0.gpr .x2 + s0.gpr .x3 := by
    rw [hmem4]; exact (keyPointerMem_fields _ _ _ _ _).2.1
  refine WP.mono (publicGenerator_ok (hs.congr hk1234.wr) h114 (by decide) hg4) fun t ⟨hmem5, hk5⟩ => ?_
  refine ⟨(hk5.gpr .x0 (by decide)).trans hdi4, ?_, ?_,
    ((hk1234.trans hk5).mono (by decide))⟩
  · intro f h1 h2
    rw [hmem5, hmem4, hmem3]
    cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 |
      (simp only [checkFieldMem, keyPointerMem, word_fieldWrite, reduceCtorEq, reduceIte, checkFieldValues]; try rfl)
  · intro x hx
    have hx' : ofs B x < 256 ∨ pWorkspace ≤ ofs B x := by omega_using [hx]
    rw [hmem5, hmem4, hmem3]
    simp only [checkFieldMem, keyPointerMem, field_write_frame _ B _ _ x hx']
    rw [hmem1]

end VG.Proof.Dsa.AArch64

end

end

/-! # Functional correctness of the AArch64 DSA domain check

The domain check is the signer's checks of a key whose public value is g:
the entry points y at g. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- The fields after the shape checks, from an entry's: the shape checks
write the digest prefix and the mask, and keep the rest. -/
theorem KeygenEntryPost.shapeFields {original s t : State} {B : Addr} {values final : Field → Addr}
    (h : KeygenEntryPost original B values s) (hf : Frm B shapeRanges s.mem t.mem)
    (hv : ∀ f, f ≠ .digestPrefixLen → f ≠ .mask → values f = final f)
    (hp : word t.mem B Field.digestPrefixLen.offset = final .digestPrefixLen)
    (hm : word t.mem B Field.mask.offset = final .mask) :
    ∀ f, word t.mem B f.offset = final f := by
  intro f
  by_cases h1 : f = .digestPrefixLen
  · subst h1; exact hp
  by_cases h2 : f = .mask
  · subst h2; exact hm
  exact ((shape_field hf f h1 h2).trans (h.fields f h1 h2)).trans (hv f h1 h2)

structure ParametersInput where
  base : Addr
  pLen : Nat
  qLen : Nat
  params : List Byte
  lengths : Spec.Dsa.lengthsValid pLen qLen
  paramsLength : params.length = 2 * pLen + qLen

namespace ParametersInput

variable (p : ParametersInput)

abbrev pb : List Byte := p.params.take p.pLen
abbrev qb : List Byte := (p.params.drop p.pLen).take p.qLen
abbrev gb : List Byte := (p.params.drop (p.pLen + p.qLen)).take p.pLen

theorem pbLength : p.pb.length = p.pLen := by
  simp only [List.length_take, p.paramsLength]; omega_using []
theorem qbLength : p.qb.length = p.qLen := component_length (by rw [p.paramsLength]; omega_using [])
theorem gbLength : p.gb.length = p.pLen := component_length (by rw [p.paramsLength]; omega_using [])

theorem pPositive : 0 < p.pb.length := by
  rw [p.pbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
theorem qPositive : 0 < p.qb.length := by
  rw [p.qbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]

abbrev accepted : Bool := shapeAccepted p.pb p.qb p.pPositive p.qPositive

theorem shapeFacts {p : ParametersInput} (ha : p.accepted = true) :
    Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.pb))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p.qb)) ∧
    Spec.Dsa.decodeBE p.pb % 2 = 1 ∧ Spec.Dsa.decodeBE p.qb % 2 = 1 := by
  rw [ParametersInput.accepted, shapeAccepted_spec] at ha
  exact of_decide_eq_true ha

def layout (original : State) (hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen) : ExecutionLayout where
  base := p.base
  pLen := p.pLen
  qLen := p.qLen
  modulus := Spec.Dsa.decodeBE p.pb
  subgroup := Spec.Dsa.decodeBE p.qb
  pInverse := 0
  qInverse := 0
  fields := checkFieldValues original p.accepted
  lengths := p.lengths
  pLength := hp
  qLength := hq

end ParametersInput

structure ParametersPre (p : ParametersInput) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  base : s.gpr .x4 = p.base
  pLength : s.gpr .x2 = BitVec.ofNat 64 p.pLen
  qLength : s.gpr .x3 = BitVec.ofNat 64 p.qLen
  paramsSource : Src s p.base usedBytes (s.gpr .x0) p.params

theorem ParametersPre.sources {p : ParametersInput} {original s : State} (h : ParametersPre p original)
    (hm : InScr p.base usedBytes original.mem s.mem) (hk : Keep coreRegs original s) :
    Src s p.base usedBytes (original.gpr .x0) p.pb ∧
    Src s p.base usedBytes (original.gpr .x0 + original.gpr .x2) p.qb ∧
    Src s p.base usedBytes (original.gpr .x0 + original.gpr .x2 + original.gpr .x3) p.gb := by
  have hsrc := h.paramsSource.congrK hm hk
  refine ⟨source_take hsrc, ?_, ?_⟩
  · rw [h.pLength]
    exact source_slice hsrc (by rw [p.paramsLength]; omega_using [])
  · rw [h.pLength, h.qLength, Offset.add_add]
    exact source_slice hsrc (by rw [p.paramsLength]; omega_using [])

structure ParametersShapePost (p : ParametersInput) (original : State)
    (hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  x0 : s.gpr .x0 = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp hq).fields f
  branch : (s.gpr .x3 == (0#64)) = !p.accepted
  frame : InScr p.base usedBytes original.mem s.mem
  keep : Keep coreRegs original s

theorem parametersShape_ok {p : ParametersInput} {s0 : State} (h : ParametersPre p s0) :
    WP isa (.seq (.block Generate.checkEntry) Checks.domainShape) s0
      (ParametersShapePost p s0 h.pLength h.qLength) := by
  refine WP.seq (WP.mono (checkEntry_ok h.scratch h.base) fun s1 he => ?_)
  have hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _⟩ := h.sources hinside (he.keep.mono (by decide))
  have hp64 : p.pb.length < 2 ^ 64 := by
    rw [p.pbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hq64 : p.qb.length < 2 ^ 64 := by
    rw [p.qbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  refine WP.mono (domainShape_ok (h.scratch.congr he.keep.wr) he.base (by decide)
    (he.fields .p (by decide) (by decide)) (he.fields .q (by decide) (by decide))
    ((he.fields .pLen (by decide) (by decide)).trans (by rw [p.pbLength]; exact h.pLength))
    ((he.fields .qLen (by decide) (by decide)).trans (by rw [p.qbLength]; exact h.qLength))
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

def ParametersPost (p : ParametersInput) (original t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 0) ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem ParametersInput.check_eq (p : ParametersInput) :
    Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params =
      (p.accepted && (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.qb)
          (Spec.Dsa.decodeBE p.pb) = 1) &&
        (decide ((Spec.Dsa.decodeBE p.pb - 1) % Spec.Dsa.decodeBE p.qb = 0) &&
        (decide (1 < Spec.Dsa.decodeBE p.gb ∧ Spec.Dsa.decodeBE p.gb < Spec.Dsa.decodeBE p.pb) &&
        (decide (1 < Spec.Dsa.decodeBE p.gb ∧ Spec.Dsa.decodeBE p.gb < Spec.Dsa.decodeBE p.pb) && true))))) := by
  rw [VG.Proof.Dsa.checkParametersBytes_eq p.lengths p.paramsLength, ParametersInput.accepted,
    shapeAccepted_spec]
  rfl

theorem toNat_ofNat_if (b : Bool) :
    BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 (if b = true then 1 else 0) := by
  cases b <;> rfl

theorem parametersRejected_ok {p : ParametersInput} {original s : State} (h : ParametersPre p original)
    (hs : ParametersShapePost p original h.pLength h.qLength s) (ha : p.accepted = false) :
    WP isa (.block [movi .x0 0]) s
      (ParametersPost p original) := by
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨hret, hmem⟩, hk⟩ => ?_
  unfold ParametersPost
  rw [p.check_eq, ha, Bool.false_and]
  exact ⟨hret,
    by rw [hmem]; exact hs.frame, (hs.keep.trans hk).mono (by decide)⟩

/-- After the workspaces: the domain's operands, with the public value g. -/
structure ParametersOperands (L : ExecutionLayout) (p : ParametersInput) (s : State) : Prop where
  generator : OperandBytes s L.base usedBytes Core.generator p.gb
  publicValue : OperandBytes s L.base usedBytes Core.publicValue p.gb
  subgroup : OperandBytes s L.base usedBytes ⟨.input .q, .qLen⟩ p.qb

def ParametersInitialized (p : ParametersInput) (original : State)
    (hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp hq).withInverses pi qi) s ∧
    ParametersOperands ((p.layout original hp hq).withInverses pi qi) p s ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    InScr p.base usedBytes original.mem s.mem ∧ Keep coreRegs original s

theorem parametersInitialize_ok {p : ParametersInput} {original st : State} (h : ParametersPre p original)
    (hs : ParametersShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces st (ParametersInitialized p original h.pLength h.qLength) := by
  let L := p.layout original h.pLength h.qLength
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hps, hqs, _⟩ := h.sources hs.frame hs.keep
  refine WP.mono (workspacesReady_ok (L := L) hs.scratch hs.x0 hs.fields hps hqs
    p.pbLength p.qbLength rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  let L' := L.withInverses pi qi
  have hr' : Ready L' t := hr
  have hframe : InScr p.base usedBytes original.mem t.mem :=
    hs.frame.trans (InScr.of_outside hf (by decide))
  have hkeep := hs.keep.trans hk
  obtain ⟨_, hqs', hgs'⟩ := h.sources hframe (hkeep.mono (by decide))
  have hpl : L'.fields .pLen = BitVec.ofNat 64 p.gb.length := by
    rw [p.gbLength]; exact h.pLength
  refine ⟨pi, qi, hr', ⟨hr'.inputOperand .g .pLen (by decide) (by decide) hgs' hpl,
    hr'.inputOperand .y .pLen (by decide) (by decide) hgs' hpl,
    hr'.inputOperand .q .qLen (by decide) (by decide) hqs' (by rw [p.qbLength]; exact h.qLength)⟩,
    hm.trans ((hs.fields .mask).trans (congrArg mask ha)),
    hframe, hkeep.mono (by decide)⟩

/-- The signer's checks of the domain, with g as the public value. -/
theorem parametersBody_ok (M : Mont) {L : ExecutionLayout} {p : ParametersInput} {s : State}
    (hr : Ready L s) (ho : ParametersOperands L p s)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup) (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hgl : p.gb.length = L.pLen) (hql : p.qb.length = L.qLen) (hqv : Spec.Dsa.decodeBE p.qb = L.subgroup)
    (hm : word s.mem L.base Field.mask.offset = mask true) :
    WP isa (.seq (Checks.signingKey M.mm) (.block SignVerify.result)) s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (signingKeyAccepted L p.gb p.gb true).toNat ∧
      Outside L.base 128 (usedBytes - 128) s.mem t.mem ∧ Keep coreRegs s t := by
  refine WP.seq (WP.mono (signingKey_ok M hr hp hq hpo hqo hpf hqf ho.generator ho.publicValue
    ho.subgroup hgl hgl hql hqv hm) fun u ⟨hu, hmu, _, hfu, hku⟩ => ?_)
  refine WP.mono (result_ok hu.scratch hu.parent.x0 (by decide) hmu) fun v ⟨hret, hmem, hkv⟩ => ?_
  exact ⟨hret,
    by rw [hmem]; exact hfu, (hku.trans hkv).mono (by decide)⟩

theorem parametersSuccess_ok (M : Mont) {p : ParametersInput} {original st : State}
    (h : ParametersPre p original)
    (hs : ParametersShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.signingKey M.mm, .block SignVerify.result]) st
      (ParametersPost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  refine WP.seq (WP.mono (parametersInitialize_ok h hs ha) fun t ⟨pi, qi, hr, ho, hm, hframe, hkeep⟩ => ?_)
  have hpf : Spec.Dsa.decodeBE p.pb ≤ 256 ^ p.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.pb; rw [p.pbLength] at hh; exact Nat.le_of_lt hh
  have hqf : Spec.Dsa.decodeBE p.qb ≤ 256 ^ p.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.qb; rw [p.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.mono (parametersBody_ok M hr ho hp1 hq255 hpo hqo hpf hqf p.gbLength p.qbLength rfl hm)
    fun v ⟨hret, hfu, hkv⟩ => ?_
  refine ⟨?_,
    hframe.trans (InScr.of_outside hfu (by decide)), (hkeep.trans hkv).mono (by decide)⟩
  rw [hret, p.check_eq, ha, Bool.true_and]
  exact toNat_ofNat_if _

theorem parametersMain_ok (M : Mont) {p : ParametersInput} {s0 : State} (h : ParametersPre p s0) :
    WP isa (Generate.checkParameters M.mm) s0 (ParametersPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (parametersShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => parametersRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval (.zero .x .x3) s = some true
    change some (s.gpr .x3 == (0#64)) = some true
    rw [hs.branch, ha]; rfl
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => parametersSuccess_ok M h hs ha)
    change eval (.zero .x .x3) s = some false
    change some (s.gpr .x3 == (0#64)) = some false
    rw [hs.branch, ha]; rfl

end VG.Proof.Dsa.AArch64
