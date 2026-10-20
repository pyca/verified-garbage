module

public import VerifiedGarbage.Proof.Dsa.AArch64.KeygenEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningKey
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
  simp only [List.length_take, p.paramsLength]; omega
theorem qbLength : p.qb.length = p.qLen := component_length (by rw [p.paramsLength]; omega)
theorem gbLength : p.gb.length = p.pLen := component_length (by rw [p.paramsLength]; omega)

theorem pPositive : 0 < p.pb.length := by
  rw [p.pbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
theorem qPositive : 0 < p.qb.length := by
  rw [p.qbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega

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
    exact source_slice hsrc (by rw [p.paramsLength]; omega)
  · rw [h.pLength, h.qLength, Offset.add_add]
    exact source_slice hsrc (by rw [p.paramsLength]; omega)

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
    rw [p.pbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  have hq64 : p.qb.length < 2 ^ 64 := by
    rw [p.qbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
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
