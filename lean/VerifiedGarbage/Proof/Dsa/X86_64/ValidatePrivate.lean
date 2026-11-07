module

public import VerifiedGarbage.Proof.Dsa.X86_64.KeygenEntry
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningKey
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSpec
public import VerifiedGarbage.Proof.Dsa.X86_64.SourceSlices
public import VerifiedGarbage.Proof.Dsa.X86_64.CoreSign
public import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceBridge
public import VerifiedGarbage.Impl.Dsa.X86_64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.PrivateKey
public import VerifiedGarbage.Proof.Dsa.X86_64.SignCompute
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.SignBytesSpec
import VerifiedGarbage.Proof.Dsa.X86_64.SigningShape
import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyFailure
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Functional correctness of the x86-64 DSA private-key validator

The validator is the signer's checks of the key (`Checks.signingKey` and
`Checks.privateKey`) after the domain check's register entry, with the
nonce field pointing at x: its range check is then x's, which the key's
consistency already includes. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def privateFieldValues (original : State) (valid : Bool) : Field → Addr
  | .p => original.gpr .rdi
  | .q => original.gpr .rdi + original.gpr .rdx
  | .g => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx
  | .y => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx
  | .x => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx + original.gpr .rdx
  | .signature => 0
  | .nonce => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx + original.gpr .rdx
  | .digest => 0
  | .out => 0
  | .pLen => original.gpr .rdx
  | .qLen => original.gpr .rcx
  | .digestLen => 0
  | .digestPrefixLen => 0
  | .mask => mask valid

/-- Point the nonce at x. -/
theorem nonceScalar_ok {s : State} {B v : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .r11 = B) (hZ : pWorkspace ≤ Z)
    (hx : word s.mem B Field.x.offset = v) :
    WP isa (.block [.mov .rax (.mem (SignVerify.initial .x)), .store (SignVerify.initial .nonce) .rax]) s fun t =>
      t.mem = s.mem.writeW (off B Field.nonce.offset) v ∧ Keep [.rax] s t := by
  refine WP.keep [.rax] ?_ rfl
  have hl (f : Field) := hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  xrun [State.ea, SignVerify.initial, h11, fieldAddress, hl .x, hw .nonce, hx]

theorem privateEntry_ok {s0 : State} {B : Addr} (hs : Scr s0 B usedBytes) (h8 : s0.gpr .r8 = B) :
    WP isa (.block PrevalidatedSign.validateEntry) s0 (KeygenEntryPost s0 B (privateFieldValues s0 true)) := by
  change WP isa (.block (([.mov .r11 (.reg .r8)] : List Instr) ++ SignVerify.save ++ checkFields ++
    SignVerify.keyPointers ++ [.mov .rax (.mem (SignVerify.initial .x)), .store (SignVerify.initial .nonce) .rax])) s0 _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (moveScratch_ok s0) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [h8] at h11
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (hs.congr hk1.2.2) h11 (by decide)) fun s2 ⟨hsaved, hf2, hk2⟩ => ?_
  have hk12 := hk1.trans hk2
  have hreg (reg : Reg) (hne : reg ≠ .r11) : s2.gpr reg = s0.gpr reg := hk12.gpr (by simpa using hne)
  have h112 : s2.gpr .r11 = B := (hk2.gpr (by decide)).trans h11
  rw [WP.block_append_iff]
  refine WP.mono (checkFields_ok (hs.congr hk12.2.2) h112 (by decide)) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .rdi (by decide), hreg .rdx (by decide), hreg .rcx (by decide)] at hmem3
  have hk123 := hk12.trans hk3
  have h113 : s3.gpr .r11 = B := (hk3.gpr (by decide)).trans h112
  have hw3 (f : Field) : word s3.mem B f.offset =
      word (checkFieldMem s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx)) B f.offset := by rw [hmem3]
  rw [WP.block_append_iff]
  refine WP.mono (keyPointers_ok (p := s0.gpr .rdi) (pl := s0.gpr .rdx) (ql := s0.gpr .rcx) (hs.congr hk123.2.2) h113 (by decide)
    ((hw3 .p).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl))
    ((hw3 .pLen).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl))
    ((hw3 .qLen).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl)))
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hk1234 := hk123.trans hk4
  have h114 : s4.gpr .r11 = B := (hk4.gpr (by decide)).trans h113
  have hx4 : word s4.mem B Field.x.offset =
      s0.gpr .rdi + s0.gpr .rdx + s0.gpr .rcx + s0.gpr .rdx + s0.gpr .rdx := by
    rw [hmem4]; exact (keyPointerMem_fields _ _ _ _ _).2.2.2
  refine WP.mono (nonceScalar_ok (hs.congr hk1234.2.2) h114 (by decide) hx4) fun t ⟨hmem5, hk5⟩ => ?_
  refine keygenEntry_finish (s := s2)
    (fun i hi => (hsaved i hi).trans (hk1.gpr (by simpa using saved_ne_r11 hi)))
    (by have := hf2; rwa [hmem1] at this) ?_ ?_ ((hk5.gpr (by decide)).trans hdi4)
    ((hk1234.trans hk5).mono (by decide))
  · intro x hx
    rw [hmem5, hmem4, hmem3]
    simp only [checkFieldMem, keyPointerMem, fieldWrite_frame _ B _ _ x hx]
  · intro f h1 h2
    rw [hmem5, hmem4, hmem3]
    cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 |
      (simp only [checkFieldMem, keyPointerMem, word_fieldWrite, reduceCtorEq, reduceIte, privateFieldValues]; try rfl)

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

def layout (original : State) (hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen) : ExecutionLayout where
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
  base : s.gpr .r8 = p.base
  pLength : s.gpr .rdx = BitVec.ofNat 64 p.pLen
  qLength : s.gpr .rcx = BitVec.ofNat 64 p.qLen
  keySource : Src s p.base usedBytes (s.gpr .rdi) p.key

theorem PrivatePre.sources {p : PrivateInput} {original s : State} (h : PrivatePre p original)
    (hm : InScr p.base usedBytes original.mem s.mem) (hk : Keep coreRegs original s) :
    Src s p.base usedBytes (original.gpr .rdi) p.components.p ∧
    Src s p.base usedBytes (original.gpr .rdi + original.gpr .rdx) p.components.q ∧
    Src s p.base usedBytes (original.gpr .rdi + original.gpr .rdx + original.gpr .rcx) p.components.g ∧
    Src s p.base usedBytes (original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx)
      p.components.y ∧
    Src s p.base usedBytes (original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx +
      original.gpr .rdx) p.components.x := by
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
    (hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  rdi : s.gpr .rdi = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp hq).fields f
  branch : s.zf = some (!p.accepted)
  saved : ∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)
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
  refine WP.mono (domainShape_ok (n := 0) (h.scratch.congr he.keep.2.2) he.base (by decide)
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
  refine ⟨h.scratch.congr hall.2.2, (hk.gpr (by decide)).trans he.base,
    he.shapeFields hf ?_ (by rw [hprefix]; rfl) hmask, hbranch,
    fun i hi => (shape_saved hf hi).trans (he.saved i hi), hinside.trans hft, hall.mono (by decide)⟩
  intro f h1 h2
  cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 | rfl

def PrivatePost (p : PrivateInput) (original t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (if Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key then 1 else 0) ∧
  (∀ i < 6, t.gpr (saved.getD i .rax) = original.gpr (saved.getD i .rax)) ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem privateRejected_ok {p : PrivateInput} {original s : State} (h : PrivatePre p original)
    (hs : PrivateShapePost p original h.pLength h.qLength s) (ha : p.accepted = false) :
    WP isa (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ VG.Impl.Bignum.X86_64.Public.exit)) s
      (PrivatePost p original) := by
  have hp := shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
  change ¬ Spec.Dsa.parametersValid (Spec.Dsa.privateKeyBytes p.pLen p.qLen p.key).params at hp
  have hv : Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key = false := by
    simp only [Spec.Dsa.validatePrivateKeyBytes, p.lengths, decide_true, Bool.not_true,
      p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    simp only [hp, decide_false, Bool.false_and]
  refine WP.mono (verifyFailure_ok hs.scratch hs.rdi (by decide))
    fun t ⟨hret, hsave, hmem, hk⟩ => ?_
  unfold PrivatePost
  rw [hv]
  exact ⟨hret, fun i hi => (hsave i hi).trans (hs.saved i hi),
    by rw [hmem]; exact hs.frame, (hs.keep.trans hk).mono (by decide)⟩

/-- After the workspaces: the key's operands, with x as the nonce. -/
structure PrivateOperands (L : ExecutionLayout) (p : PrivateInput) (s : State) : Prop where
  generator : OperandBytes s L.base usedBytes Core.generator p.components.g
  publicValue : OperandBytes s L.base usedBytes Core.publicValue p.components.y
  subgroup : OperandBytes s L.base usedBytes ⟨.input .q, .qLen⟩ p.components.q
  privateScalar : OperandBytes s L.base usedBytes Core.privateScalar p.components.x
  nonce : OperandBytes s L.base usedBytes Core.nonce p.components.x

def PrivateInitialized (p : PrivateInput) (original : State)
    (hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp hq).withInverses pi qi) s ∧
    PrivateOperands ((p.layout original hp hq).withInverses pi qi) p s ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    (∀ i < 6, word s.mem p.base (8 * i) = original.gpr (saved.getD i .rax)) ∧
    InScr p.base usedBytes original.mem s.mem ∧ Keep coreRegs original s

theorem privateInitialize_ok {p : PrivateInput} {original st : State} (h : PrivatePre p original)
    (hs : PrivateShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces st (PrivateInitialized p original h.pLength h.qLength) := by
  let L := p.layout original h.pLength h.qLength
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hps, hqs, _⟩ := h.sources hs.frame hs.keep
  refine WP.mono (workspacesReady_ok (L := L) hs.scratch hs.rdi hs.fields hps hqs
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
    fun i hi => (hf.word (Or.inl (by omega)) (by omega)).trans (hs.saved i hi),
    hframe, hkeep.mono (by decide)⟩

theorem and_redundant {a b c : Bool} (h : b = true → c = true) : (a && b && c) = (a && b) := by
  cases a <;> cases b <;> simp_all

/-- With x as the nonce, the signer's acceptance of the key is its validation:
the nonce's range check is x's, which `keyValid` already includes. -/
theorem PrivateInput.validate_eq (p : PrivateInput) {pi qi : BitVec 64} {original : State}
    {hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen} {hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen}
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

theorem privateSuccess_ok (M : Mont) (Sq : MontS) {p : PrivateInput} {original st : State}
    (h : PrivatePre p original)
    (hs : PrivateShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
      .block SignVerify.result]) st (PrivatePost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  refine WP.seq (WP.mono (privateInitialize_ok h hs ha) fun t ⟨pi, qi, hr, ho, hm, hsv, hframe, hkeep⟩ => ?_)
  let L := (p.layout original h.pLength h.qLength).withInverses pi qi
  have hpf : L.modulus ≤ 256 ^ L.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.p; rw [p.components.pLength] at hh; exact Nat.le_of_lt hh
  have hqf : L.subgroup ≤ 256 ^ L.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.q; rw [p.components.qLength] at hh; exact Nat.le_of_lt hh
  refine WP.seq (WP.mono (signingKey_ok M Sq hr hp1 hq255 hpo hqo hpf hqf ho.generator ho.publicValue
    ho.subgroup p.components.gLength p.components.yLength p.components.qLength rfl hm)
    fun u ⟨hu, hmu, _, hfu, hku⟩ => ?_)
  have hg1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.generator]) ho.generator
  have hy1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.publicValue]) ho.publicValue
  have hx1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.privateScalar]) ho.privateScalar
  have hn1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.nonce]) ho.nonce
  refine WP.seq (WP.mono (privateKey_ok M Sq hu hp1 hpo hg1 hy1 hx1 hn1 p.components.gLength
    p.components.yLength p.xLength p.xLength hmu) fun w ⟨hw, hmw, _, hfw, hkw⟩ => ?_)
  have hmv : word w.mem L.base Field.mask.offset =
      mask (Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key) :=
    hmw.trans (congrArg mask ((privateAccepted_signingKey L p.values p.components.y true hp1 hpf).trans
      (p.validate_eq ha)))
  refine WP.mono (result_ok hw.scratch hw.parent.rdi (by decide) hmv) fun v ⟨hret, hsave, hmem, hkv⟩ => ?_
  refine ⟨?_, fun i hi => ((hsave i hi).trans ((hfu.trans hfw).word (Or.inl (by omega)) (by omega))).trans (hsv i hi),
    ?_, (((hkeep.trans hku).trans hkw).trans hkv).mono (by decide)⟩
  · rw [hret]; exact toNat_ofNat_if _
  · rw [hmem]; exact hframe.trans (InScr.of_outside (hfu.trans hfw) (by decide))

theorem privateMain_ok (M : Mont) (Sq : MontS) {p : PrivateInput} {s0 : State} (h : PrivatePre p s0) :
    WP isa (PrevalidatedSign.validate Sq.mm M.mm) s0 (PrivatePost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (privateShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => privateRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => privateSuccess_ok M Sq h hs ha)
    change eval .e s = some false
    simp only [eval, hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.X86_64
