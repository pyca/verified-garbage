module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedSignVerified
-- Proofs inside exposed definitions (structure values) use these: Lean needs them public.
public import VerifiedGarbage.Proof.Bignum.Octets -- shake: keep
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSlices
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
public import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
public import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningInput
public import VerifiedGarbage.Proof.Dsa.X86_64.CoreSign
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningShape
public import VerifiedGarbage.Impl.Dsa.X86_64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.SignBody
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
meta import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningInput
meta import VerifiedGarbage.Proof.Dsa.X86_64.CoreSign
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningShape
meta import VerifiedGarbage.Impl.Dsa.X86_64.PrevalidatedSign
meta import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignBody
meta import VerifiedGarbage.Proof.Dsa.X86_64.Result
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
meta import VerifiedGarbage.Proof.Dsa.X86_64.Save
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.X86_64.ValidatePrivateCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.ValidatePrivate`, which only this module used -/

section

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
  packedComponents p.pLen p.qLen p.key (by rw [p.keyLength]; omega_using [])

theorem xLength : p.components.x.length = p.qLen := component_length (by rw [p.keyLength]; omega_using [])

theorem pPositive : 0 < p.components.p.length := by
  rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
theorem qPositive : 0 < p.components.q.length := by
  rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]

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
    exact source_slice hsrc (by rw [p.keyLength]; omega_using [])
  · rw [h.pLength, h.qLength, Offset.add_add]
    exact source_slice hsrc (by rw [p.keyLength]; omega_using [])
  · rw [h.pLength, h.qLength, Offset.add_add, Offset.add_add,
      show p.pLen + (p.qLen + p.pLen) = 2 * p.pLen + p.qLen by omega_using []]
    exact source_slice hsrc (by rw [p.keyLength]; omega_using [])
  · rw [h.pLength, h.qLength, Offset.add_add, Offset.add_add, Offset.add_add,
      show p.pLen + (p.qLen + (p.pLen + p.pLen)) = 3 * p.pLen + p.qLen by omega_using []]
    exact source_slice hsrc (by rw [p.keyLength]; omega_using [])

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
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hq64 : p.components.q.length < 2 ^ 64 := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
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
    fun i hi => (hf.word (Or.inl (by omega_using [hi])) (by omega_using [hi])).trans (hs.saved i hi),
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
  refine ⟨?_, fun i hi => ((hsave i hi).trans ((hfu.trans hfw).word (Or.inl (by omega_using [hi])) (by omega_using [hi]))).trans (hsv i hi),
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

end

end

/-! # Constant time of the x86-64 DSA private-key validator

Two calls with the same pointers, lengths and public key components take
the same path, whatever their private scalars and scratch hold. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure PrivateCall where
  input : PrivateInput
  original : State
  pre : PrivatePre input original

abbrev PrivateCall.layout (c : PrivateCall) : ExecutionLayout :=
  c.input.layout c.original c.pre.pLength c.pre.qLength

structure PrivateAgrees (reference c : PrivateCall) : Prop where
  layout : c.layout = reference.layout
  pBytes : c.input.components.p = reference.input.components.p
  qBytes : c.input.components.q = reference.input.components.q

def PrivateStart (reference : PrivateCall) (s : State) : Prop :=
  ∃ c : PrivateCall, PrivateAgrees reference c ∧ c.original = s

def PrivateEntered (reference : PrivateCall) (s : State) : Prop :=
  ∃ c : PrivateCall, PrivateAgrees reference c ∧
    KeygenEntryPost c.original c.input.base (privateFieldValues c.original true) s

def PrivateShaped (reference : PrivateCall) (s : State) : Prop :=
  ∃ c : PrivateCall, PrivateAgrees reference c ∧
    PrivateShapePost c.input c.original c.pre.pLength c.pre.qLength s

def PrivateReady (reference : PrivateCall) (s : State) : Prop :=
  ∃ c : PrivateCall, PrivateAgrees reference c ∧
    PrivateInitialized c.input c.original c.pre.pLength c.pre.qLength s

theorem PrivateAgrees.pLen {reference c : PrivateCall} (h : PrivateAgrees reference c) :
    c.input.pLen = reference.input.pLen := congrArg ExecutionLayout.pLen h.layout

theorem PrivateAgrees.qLen {reference c : PrivateCall} (h : PrivateAgrees reference c) :
    c.input.qLen = reference.input.qLen := congrArg ExecutionLayout.qLen h.layout

theorem PrivateAgrees.accepted {reference c : PrivateCall} (h : PrivateAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold PrivateInput.accepted
  congr 1
  · exact h.pBytes
  · exact h.qBytes

theorem privateEntry_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .r8 = B))
    (.block PrevalidatedSign.validateEntry) (fun _ _ => True) :=
  two_taint [.r8] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

theorem privateEntered_ct : RelCT isa (Two PrivateStart) (.block PrevalidatedSign.validateEntry)
    (Two PrivateEntered) := by
  refine two_post (two_map (fun c : PrivateCall => c.layout.base) ?_ privateEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact c.pre.base.trans (congrArg ExecutionLayout.base ha.layout)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (privateEntry_ok c.pre.scratch c.pre.base) fun t ht => ⟨c, ha, ht⟩

def PrivateCall.shape (c : PrivateCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  digestLen := 0
  extentBound := by decide
  pPositive := c.input.pPositive
  qPositive := c.input.qPositive
  pBound := by
    rw [c.input.components.pLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega_using [this]
  qBound := by
    rw [c.input.components.qLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega_using [this]
  digestBound := by decide

theorem PrivateAgrees.shape {reference c : PrivateCall} (h : PrivateAgrees reference c) :
    c.shape = reference.shape := by
  unfold PrivateCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pBytes
  · exact h.qBytes

theorem PrivateEntered.context {reference : PrivateCall} {s : State} (h : PrivateEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _⟩ := c.pre.sources hf (he.keep.mono (by decide))
  refine ⟨c.pre.scratch.congr he.keep.2.2, he.base, he.fields .p (by decide) (by decide),
    he.fields .q (by decide) (by decide), ?_, ?_, he.fields .digestLen (by decide) (by decide), hps, hqs⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.components.p.length
    rw [c.input.components.pLength]
    exact (he.fields .pLen (by decide) (by decide)).trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.components.q.length
    rw [c.input.components.qLength]
    exact (he.fields .qLen (by decide) (by decide)).trans c.pre.qLength

theorem privateShape_ct : RelCT isa (Two PrivateStart)
    (.seq (.block PrevalidatedSign.validateEntry) Checks.domainShape) (Two PrivateShaped) := by
  refine two_post (RelCT.seq privateEntered_ct
    (two_map PrivateCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (privateShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

theorem PrivateShaped.branch {reference : PrivateCall} {s : State} (h : PrivateShaped reference s) :
    eval .e s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change s.zf = _
  rw [hs.branch, ha.accepted]

theorem PrivateShaped.rdi {reference : PrivateCall} {s : State} (h : PrivateShaped reference s) :
    s.gpr .rdi = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.rdi.trans (congrArg ExecutionLayout.base ha.layout)

def PrivateCall.initialization (c : PrivateCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  pLength := c.input.components.pLength
  qLength := c.input.components.qLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem PrivateShaped.initialization {reference : PrivateCall} {s : State}
    (h : PrivateShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  obtain ⟨hps, hqs, _⟩ := c.pre.sources hs.frame hs.keep
  have hps' : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.components.p := hps
  have hqs' : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.components.q := hqs
  rw [hag.layout] at hf hr hscr hps' hqs'
  rw [hag.pBytes] at hps'
  rw [hag.qBytes] at hqs'
  exact ⟨hscr, hr, hf, hps', hqs'⟩

abbrev AcceptedPrivateCall := {c : PrivateCall // c.input.accepted = true}

theorem privateWorkspaces_ct : RelCT isa (Two (fun c : AcceptedPrivateCall => PrivateShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedPrivateCall => PrivateReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedPrivateCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (privateInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

/-- The key's operands, as the schedule reads them. -/
def privateInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.publicValue, p.layout.pLen), (⟨.input .q, .qLen⟩, p.layout.qLen), (Core.generator, p.layout.pLen),
    (Core.privateScalar, p.layout.qLen), (Core.nonce, p.layout.qLen)]

theorem privateInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ privateInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [privateInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · simp [Core.generator, stablePointer]
  · simp [Core.privateScalar, stablePointer]
  · simp [Core.nonce, stablePointer]

def PrivateCall.schedule (c : PrivateCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := 0
  pGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).1
  qGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).2.1
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2
  pFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.p
    rw [c.input.components.pLength] at h
    exact Nat.le_of_lt h
  qFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.q
    rw [c.input.components.qLength] at h
    exact Nat.le_of_lt h
  digestBound := by decide

theorem PrivateReady.body {reference : PrivateCall} {s : State} (ha : reference.input.accepted = true)
    (h : PrivateReady reference s) : ∃ pi qi, PublicKeyPre privateInputs (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _, _⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change PrivateOperands (c.layout.withInverses pi qi) c.input s at ho
  rw [hag.layout] at hr ho hmask
  have hpl (bs : List Byte) (hb : bs.length = c.input.pLen) : bs.length = reference.layout.pLen :=
    hb.trans hag.pLen
  have hql (bs : List Byte) (hb : bs.length = c.input.qLen) : bs.length = reference.layout.qLen :=
    hb.trans hag.qLen
  refine ⟨pi, qi, ⟨hr, ?_, ⟨true, hmask⟩⟩, c.input.components.q, ho.subgroup,
    hql _ c.input.components.qLength, ?_⟩
  · intro a ha
    simp only [privateInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, ho.publicValue, hpl _ c.input.components.yLength⟩
    · exact ⟨_, ho.subgroup, hql _ c.input.components.qLength⟩
    · exact ⟨_, ho.generator, hpl _ c.input.components.gLength⟩
    · exact ⟨_, ho.privateScalar, hql _ c.input.xLength⟩
    · exact ⟨_, ho.nonce, hql _ c.input.xLength⟩
  · change Spec.Dsa.decodeBE c.input.components.q = Spec.Dsa.decodeBE reference.input.components.q
    rw [hag.qBytes]

theorem privateReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedPrivateCall => PrivateReady c.val) s₁ s₂) :
    Two (PublicKeyPre privateInputs) s₁ s₂ := by
  obtain ⟨reference, h₁, h₂⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂⟩

theorem privateBody_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (PublicKeyPre privateInputs))
    (seqs [Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm, .block SignVerify.result])
    (fun _ _ => True) := by
  have h1 := signingKey_ct M Sq privateInputs (fun p => privateInputs_stable p)
    (by intro p; simp [privateInputs]) (by intro p; simp [privateInputs])
    (by intro p; simp [privateInputs])
  have h2 := privateKey_ct M Sq privateInputs (fun p => privateInputs_stable p)
    (by intro p; simp [privateInputs]) (by intro p; simp [privateInputs])
    (by intro p; simp [privateInputs]) (by intro p; simp [privateInputs])
  unfold seqs
  refine RelCT.seq h1 (RelCT.seq h2 ?_)
  exact two_map (fun p => p.layout.base) (fun _ _ h => h.1.parent.rdi) result_ct

theorem privateSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedPrivateCall => PrivateShaped c.val))
      (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
        .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq privateWorkspaces_ct ?_
  exact (privateBody_ct M Sq).mono (fun _ _ h => privateReady_related h) (fun _ _ h => h)

theorem privateMain_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two PrivateStart) (PrevalidatedSign.validate Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq privateShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : PrivateCall => c.layout.base) (fun _ _ h => h.rdi) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (privateSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # The x86-64 DSA private-key validator verified against its contract

`validating_private_verified` is the program's proof;
`validating_private_call_verified` that of the code that calls the
Montgomery kernels, whose return addresses take eight bytes of stack. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64

structure PrivateABI (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩]
  wr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩]
  keyScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩
  retKey : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat * 8⟩
  keyBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  scratchBound : (s.gpr .r8).toNat + (s.gpr .r9).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .rdx).toNat (s.gpr .rcx).toNat
  keyLength : (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat + 2 * (s.gpr .rcx).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .rdx).toNat ≤ (s.gpr .r9).toNat

theorem privateABI_of {s : State} (h : (Spec.Dsa.validatePrivateKeyContract abi).pre s) : PrivateABI s := by
  sig_pre [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero] at h
  sig_split h
  constructor <;> with_reducible assumption

def PrivateABI.input {s : State} (h : PrivateABI s) : PrivateInput where
  base := s.gpr .r8
  pLen := (s.gpr .rdx).toNat
  qLen := (s.gpr .rcx).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength

theorem PrivateABI.used {s : State} (h : PrivateABI s) : usedBytes ≤ (s.gpr .r9).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega_using [hl, hs]

theorem PrivateABI.pre {s : State} (h : PrivateABI s) : PrivatePre h.input s := by
  have hs : Scr s (s.gpr .r8) ((s.gpr .r9).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  exact ⟨scratch_prefix hs h.used (by decide), rfl, (ofNat_toNat64 _).symm, (ofNat_toNat64 _).symm,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt) h.keyScratch) h.used⟩

def PrivateABI.call {s : State} (h : PrivateABI s) : PrivateCall := ⟨h.input, s, h.pre⟩

theorem privateGprPreserved {s t : State} (h : PrivateABI s) (hp : PrivatePost h.input s t) :
    gprPreserved s t := by
  obtain ⟨_, hsaved, hf, hk⟩ := hp
  refine ⟨?_, Mem.readW_congr fun i hi => ?_⟩
  · intro reg hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · exact hk.gpr (by decide)
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · exact hf _ (Nat.le_trans h.used (out_scr h.retScratch
      (contains_byte (s.gpr .rsp) (i := i) (len := 8) hi (by decide))))

theorem privateSharedPost {s t : State} (h : PrivateABI s) (hp : PrivatePost h.input s t) :
    (Spec.Dsa.validatePrivateKeyContract abi).post s t := by
  sig_post [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero]
  rw [hp.1]
  change _ = if Spec.Dsa.validatePrivateKeyBytes h.input.pLen h.input.qLen h.input.key = true then 1 else 0
  cases Spec.Dsa.validatePrivateKeyBytes h.input.pLen h.input.qLen h.input.key <;> rfl

theorem validatingPrivateCorrect (M : Mont) (Sq : MontS)
    (hmx : (PrevalidatedSign.validate Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.validatePrivateKeyContract abi).pre s) :
    ∃ trace t, Exec isa (PrevalidatedSign.validate Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.validatePrivateKeyContract abi).post s t := by
  have ha := privateABI_of h
  obtain ⟨trace, t, he, hp⟩ := privateMain_ok M Sq ha.pre
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (privateGprPreserved ha hp), privateSharedPost ha hp⟩

theorem privatePublicRelated {s₁ s₂ : State} (h₁ : PrivateABI s₁) (h₂ : PrivateABI s₂)
    (h : (Spec.Dsa.validatePrivateKeyContract abi).pub s₁ s₂) : Two PrivateStart s₁ s₂ := by
  sig_pub [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs,
    stackArgs_zero] at h
  obtain ⟨_, hl, hdi, _, hdx, hcx, h8, _⟩ := h
  have hpubl := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpubl
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat hdx
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat hcx
  have hpub : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
      h₂.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) := by
    have hb' : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
        h₂.input.key.take (3 * h₂.input.pLen + h₂.input.qLen) := hb
    rw [← hp, ← hq] at hb'
    exact hb'
  have hpb : h₁.input.components.p = h₂.input.components.p := by
    have he := prefix_component_eq (offset := 0) (len := h₁.input.pLen) hpub (by omega_using [])
    simp only [List.drop_zero] at he
    change h₁.input.key.take h₁.input.pLen = h₂.input.key.take h₂.input.pLen
    rw [← hp]
    exact he
  have hqb : h₁.input.components.q = h₂.input.components.q := by
    have he := prefix_component_eq (offset := h₁.input.pLen) (len := h₁.input.qLen) hpub (by omega_using [])
    change (h₁.input.key.drop h₁.input.pLen).take h₁.input.qLen =
      (h₂.input.key.drop h₂.input.pLen).take h₂.input.qLen
    rw [← hp, ← hq]
    exact he
  have hac : h₁.input.accepted = h₂.input.accepted := by
    unfold PrivateInput.accepted
    congr 1
  have hlayout : h₁.call.layout = h₂.call.layout := by
    change h₁.input.layout s₁ _ _ = h₂.input.layout s₂ _ _
    unfold PrivateInput.layout
    have hf : privateFieldValues s₁ h₁.input.accepted = privateFieldValues s₂ h₂.input.accepted := by
      funext f
      cases f <;> simp only [privateFieldValues, hdi, hdx, hcx, hac]
    congr 1
    · exact congrArg Spec.Dsa.decodeBE hpb
    · exact congrArg Spec.Dsa.decodeBE hqb
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hpb, hqb⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl, rfl⟩, rfl⟩⟩

theorem validatingPrivateConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (Spec.Dsa.validatePrivateKeyContract abi).pre
      (Spec.Dsa.validatePrivateKeyContract abi).pub (PrevalidatedSign.validate Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (privateMain_ct M Sq _ _ _ _ _ _
    (privatePublicRelated (privateABI_of h₁) (privateABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero key is
allowed by the contract and rejected by the program. -/
def privateSatState : State where
  gpr r := match r with
    | .rdi => 0x2000 | .rsi => 424 | .rdx => 128 | .rcx => 20
    | .r8 => 0x8000 | .r9 => 2048 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 424⟩]
  wr := [⟨0x8000, 16384⟩]

theorem validatingPrivateSatisfiable : ∃ s, (Spec.Dsa.validatePrivateKeyContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs,
    stackArgs_zero] [privateSatState, Mem.readW, Mem.read] using privateSatState

theorem validating_private_verified (M : Mont) (Sq : MontS)
    (hmx : (PrevalidatedSign.validate Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (PrevalidatedSign.validate Sq.mm M.mm) (Spec.Dsa.validatePrivateKeyContract abi) :=
  ⟨validatingPrivateCorrect M Sq hmx, validatingPrivateConstantTime M Sq, validatingPrivateSatisfiable⟩

theorem validatingPrivate_implies8 :
    (Spec.Dsa.validatePrivateKeyContract abi).Implies (Spec.Dsa.validatePrivateKeyContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero,
      List.range, List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero,
      List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs,
    stackArgs_zero, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs,
      stackArgs_zero, List.range, List.range.loop]
      [privateSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using privateSatState

theorem validatingPrivate_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hp : (Spec.Dsa.validatePrivateKeyContract abi).post s b) :
    (Spec.Dsa.validatePrivateKeyContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  sig_post [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, stackArgs_zero,
    List.range, List.range.loop] at hp ⊢
  simpa only [State.patch_gpr] using hp

theorem validating_private_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = PrevalidatedSign.validate Sq.mm M.mm)
    (hmx : (PrevalidatedSign.validate Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.validatePrivateKeyContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ validatingPrivateCorrect M Sq hmx) (hin ▸ validatingPrivateConstantTime M Sq)
    validatingPrivate_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    (fun s b hv u _ _ hp => validatingPrivate_patch s b hv u hp)

end VG.Proof.Dsa.X86_64
