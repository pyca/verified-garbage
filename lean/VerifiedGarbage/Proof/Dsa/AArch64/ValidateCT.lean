module

public import VerifiedGarbage.Proof.Dsa.AArch64.ParametersCT
public import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceBridge
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceBridge
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingCT
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInitialize
public import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.AArch64.Result
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedFields
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
public import VerifiedGarbage.Impl.Dsa.AArch64.Workspace
public import VerifiedGarbage.Proof.Dsa.AArch64.Execution
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInput
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.AArch64.Finish
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Spec.Dsa.Prevalidated
meta import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Result
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInitialize
meta import Mathlib.Algebra.Group.Nat.Defs
meta import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
meta import VerifiedGarbage.Proof.Dsa.AArch64.InitializedFields
meta import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
meta import VerifiedGarbage.Impl.Dsa.AArch64.Workspace
meta import VerifiedGarbage.Proof.Dsa.AArch64.Execution
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInput
meta import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
meta import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.AArch64.Finish
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Dsa.AArch64.ComputeCT
import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.SharedCall
import VerifiedGarbage.Proof.Dsa.AArch64.SharedCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ComputeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedCallCT
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.CoreSign
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.EntryCT
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyCompute
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABI
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSlices
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
public import VerifiedGarbage.Proof.Dsa.AArch64.CoreVerify
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
public import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyCompute
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSpec
public import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
public import VerifiedGarbage.Impl.Dsa.AArch64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveChecked
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parameters
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSpec
meta import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
meta import VerifiedGarbage.Proof.Dsa.AArch64.CoreSign
meta import VerifiedGarbage.Impl.Dsa.AArch64.PrevalidatedSign
meta import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveChecked
meta import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState

/-! ### `Dsa.AArch64.ValidatePrivateCT`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.ValidatePrivate`, which only this module used -/

section

/-! # Functional correctness of the AArch64 DSA private-key validator

The validator is the signer's checks of the key after the domain check's
register entry, with the nonce field pointing at x: its range check is then
x's, which the key's consistency already includes. The two exponentiations
of those checks, y = g^x and the domain's `g^q = 1`, are one pass over both
exponents (`SharedPower.pow`). -/

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
  obtain hk123 := hk1.trans hk3
  obtain h113 : s3.gpr .x11 = B := (hk3.gpr .x11 (by decide)).trans h11
  have hw3 (f : Field) : word s3.mem B f.offset =
      word (checkFieldMem s1.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3)) B f.offset := by rw [hmem3]
  rw [WP.block_append_iff]
  refine WP.mono (keyPointers_ok (p := s0.gpr .x0) (pl := s0.gpr .x2) (ql := s0.gpr .x3) (hs.congr hk123.wr) h113 (by decide)
    ((hw3 .p).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl))
    ((hw3 .pLen).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl))
    ((hw3 .qLen).trans (by simp only [checkFieldMem, word_fieldWrite]; rfl)))
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  obtain hk1234 := hk123.trans hk4
  obtain h114 : s4.gpr .x11 = B := (hk4.gpr .x11 (by decide)).trans h113
  obtain hx4 : word s4.mem B Field.x.offset =
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
    obtain hx' : ofs B x < 256 ∨ pWorkspace ≤ ofs B x := by omega_using [hx]
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
  obtain hsrc := h.keySource.congrK hm hk
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
  obtain hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _⟩ := h.sources hinside (he.keep.mono (by decide))
  obtain hp64 : p.components.p.length < 2 ^ 64 := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  obtain hq64 : p.components.q.length < 2 ^ 64 := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  refine WP.mono (domainShape_ok (h.scratch.congr he.keep.wr) he.base (by decide)
    (he.fields .p (by decide) (by decide)) (he.fields .q (by decide) (by decide))
    ((he.fields .pLen (by decide) (by decide)).trans (by rw [p.components.pLength]; exact h.pLength))
    ((he.fields .qLen (by decide) (by decide)).trans (by rw [p.components.qLength]; exact h.qLength))
    hps hqs p.pPositive hp64 p.qPositive hq64 rfl rfl (by decide)
    (he.fields .digestLen (by decide) (by decide))) fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  obtain hall := he.keep.trans hk
  obtain hft : InScr p.base usedBytes s1.mem s2.mem := by
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
  obtain hp := shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
  change ¬ Spec.Dsa.parametersValid (Spec.Dsa.privateKeyBytes p.pLen p.qLen p.key).params at hp
  obtain hv : Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key = false := by
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
  obtain hframe : InScr p.base usedBytes original.mem t.mem :=
    hs.frame.trans (InScr.of_outside hf (by decide))
  obtain hkeep := hs.keep.trans hk
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
  obtain hpf : L.modulus ≤ 256 ^ L.pLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.components.p
    rw [p.components.pLength] at hh
    exact Nat.le_of_lt hh
  rw [privateAccepted_spec L p.values p.components.y hsize hpodd hqodd hpf p.components.yLength,
    and_redundant (fun hkv => ?_)]
  · simp only [Spec.Dsa.validatePrivateKeyBytes, p.lengths, decide_true, Bool.not_true,
      p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only [Spec.Dsa.keyValid, Bool.and_eq_true, decide_eq_true_eq] at hkv
    exact decide_eq_true ⟨hkv.2.1.1, hkv.2.1.2⟩

/-- The private key's checks: x's and the nonce's ranges, `g^x = y`, and
`g^q = 1` with it. -/
theorem privateChecks_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hop : L.modulus % 2 = 1)
    {gb yb xb nb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hx : OperandBytes s0 L.base usedBytes Core.privateScalar xb)
    (hn : OperandBytes s0 L.base usedBytes Core.nonce nb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen)
    (hxl : xb.length = L.qLen) (hnl : nb.length = L.qLen) (hqbl : qb.length = L.qLen)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar, Checks.range qWorkspace Core.nonce,
        SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t),
        Checks.equal (Core.element t) Core.publicValue]) s0 fun s4 =>
      Ready L s4 ∧
      word s4.mem L.base Field.mask.offset =
        mask (decide (Spec.Dsa.encodeBE L.pLen (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE xb) L.modulus) = yb) &&
          (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE qb) L.modulus = 1) &&
          (decide (0 < Spec.Dsa.decodeBE nb ∧ Spec.Dsa.decodeBE nb < L.subgroup) &&
          (decide (0 < Spec.Dsa.decodeBE xb ∧ Spec.Dsa.decodeBE xb < L.subgroup) && valid)))) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s4.mem ∧ Keep coreRegs s0 s4 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  obtain ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega_using [hpu]
  unfold seqs
  refine WP.seq (WP.mono (readyRange_ok h0 .q Core.privateScalar (by trivial) hx.active
    (by rw [hxl]; omega_using [hql]) (by simp only [hxl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm) fun s1 h1 => ?_)
  obtain hg1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg
  obtain hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  obtain hx1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.privateScalar]) hx
  obtain hn1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.nonce]) hn
  obtain hq1 := h1.preserve h0 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb
  refine WP.seq (WP.mono (readyRange_ok h1.ready .q Core.nonce (by trivial) hn1.active
    (by rw [hnl]; omega_using [hql]) (by simp only [hnl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false h1.mask) fun s2 h2 => ?_)
  obtain hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  obtain hy2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy1
  obtain hx2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.privateScalar]) hx1
  obtain hq2 := h2.preserve h1.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq1
  refine WP.seq (WP.mono (SharedPower.readySharedPow_ok M h2.ready hp hop Core.generator Core.privateScalar
    (by trivial) (by trivial) hg2.active hx2.active hq2.active.source (hqbl.trans hxl.symm)
    (by rw [hgl]; omega_using [hql, hqp]) (by rw [hgl]) (by rw [hxl]; omega_using [hql])
    (by rw [hxl]; omega_using [hqu]) t (by decide) ht h2.mask) fun s3 ⟨u, h3, h3c⟩ => ?_)
  obtain hy3 := h3c.preserve h3.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue])
    (h3.external (by decide) ht hy2)
  obtain hout := h3c.preserve h3.ready (Nat.le_refl _) (by change Field.pLen ≠ .mask; decide) (by trivial)
    (h3.output (by decide) ht)
  refine WP.mono (readyEqual_ok h3c.ready (Core.element t) Core.publicValue
    (by change t < 2 ^ 16; decide) (by trivial) hout hy3.active
    (by simp only [encodeBE_length, ModulusSide.length, hyl])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql, hqp])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hpu]) false h3c.mask) fun s4 h4 => ?_
  refine ⟨h4.ready, ?_,
    (((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans
      h3c.scheduleFrame).trans h4.scheduleFrame,
    ((((h1.keep.trans h2.keep).trans h3.keep).trans h3c.keep).trans h4.keep).mono (by decide)⟩
  have hm4 := h4.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length, ModulusSide.value] at hm4
  exact hm4

theorem and_swap (e g n x v : Bool) : (e && (g && (n && (x && v)))) = (e && (n && (x && (g && v)))) := by
  cases e <;> cases g <;> cases n <;> cases x <;> rfl

theorem privateSuccess_ok (M : Mont) {p : PrivateInput} {original st : State}
    (h : PrivatePre p original)
    (hs : PrivateShapePost p original h.pLength h.qLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, seqs (Checks.publicPrefix M.mm),
      Checks.range qWorkspace Core.privateScalar, Checks.range qWorkspace Core.nonce,
      SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t),
      Checks.equal (Core.element t) Core.publicValue, .block SignVerify.result]) st (PrivatePost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  refine WP.seq (WP.mono (privateInitialize_ok h hs ha) fun s1 ⟨pi, qi, hr, ho, hm, hframe, hkeep⟩ => ?_)
  let L := (p.layout original h.pLength h.qLength).withInverses pi qi
  obtain hpf : L.modulus ≤ 256 ^ L.pLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.components.p; rw [p.components.pLength] at hh; exact Nat.le_of_lt hh
  obtain hqf : L.subgroup ≤ 256 ^ L.qLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.components.q; rw [p.components.qLength] at hh; exact Nat.le_of_lt hh
  refine WP.seq (WP.mono (keyPrefix_ok M hr hp1 hq255 hpo hqo hpf hqf ho.generator ho.publicValue
    ho.subgroup p.components.gLength p.components.yLength hm) fun u ⟨hu, hmu, hfu, hku⟩ => ?_)
  obtain hg1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.generator]) ho.generator
  obtain hy1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.publicValue]) ho.publicValue
  obtain hx1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.privateScalar]) ho.privateScalar
  obtain hn1 := hr.preserveExternal hu hfu hku (by decide) (by simp [stablePointer, Core.nonce]) ho.nonce
  obtain hq1 := hr.preserveExternal hu hfu hku (by decide) (by change Field.q ≠ .mask; decide) ho.subgroup
  apply wpAppendSequences (a := [Checks.range qWorkspace Core.privateScalar, Checks.range qWorkspace Core.nonce,
    SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t),
    Checks.equal (Core.element t) Core.publicValue]) (b := [.block SignVerify.result]) (by simp) (by simp)
  refine WP.mono (privateChecks_ok M hu hp1 hpo hg1 hy1 hx1 hn1 hq1 p.components.gLength
    p.components.yLength p.xLength p.xLength p.components.qLength hmu) fun w ⟨hw, hmw, hfw, hkw⟩ => ?_
  obtain hmv : word w.mem L.base Field.mask.offset =
      mask (Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key) :=
    hmw.trans (congrArg mask ((and_swap _ _ _ _ _).trans
      ((privateAccepted_signingKey L p.values p.components.y true hp1 hpf).trans (p.validate_eq ha))))
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

end

end

/-! ### `Dsa.AArch64.PrevalidatedCT`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.PrevalidatedBody`, which this module and modules that import it used -/

section

/-! # Verification computation, result return and ABI register restoration -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/PrevalidatedCompute.lean`, which only this module imported.
section

/-! # Verification computation, for a validated immutable public key -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def prevalidatedAccepted (L : ExecutionLayout) (data : VerifyValues) (valid : Bool) : Bool :=
  decide (Spec.Dsa.encodeBE L.qLen (data.value L) = data.signatureR) &&
  (decide (0 < Spec.Dsa.decodeBE data.signatureS ∧ Spec.Dsa.decodeBE data.signatureS < L.subgroup) &&
  (decide (0 < Spec.Dsa.decodeBE data.signatureR ∧ Spec.Dsa.decodeBE data.signatureR < L.subgroup) &&
    valid))

theorem prevalidatedCompute_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues)
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue data.publicValue)
    (hr : OperandBytes s0 L.base usedBytes Core.signatureR data.signatureR)
    (hs : OperandBytes s0 L.base usedBytes Core.signatureS data.signatureS)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen) (hyl : data.publicValue.length = L.pLen)
    (hrl : data.signatureR.length = L.qLen) (hsl : data.signatureS.length = L.qLen)
    (hzl : data.digest.length < 2 ^ 64)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (Prevalidated.compute M.mm) s0 fun s5 =>
      Ready L s5 ∧ word s5.mem L.base Field.mask.offset = mask (prevalidatedAccepted L data valid) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s5.mem ∧ Keep coreRegs s0 s5 := by
  obtain ⟨hql, hqu, _, _⟩ := L.widths
  obtain hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega_using [hqu]
  obtain hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega_using [hqu]
  unfold Prevalidated.compute
  refine WP.seq (WP.mono (readyMinus_ok h0 .q 2 (by decide)
    (by change 2 ≤ L.subgroup; omega_using [hq]) qMinusTwo (by decide) hqm) fun s1 h1 => ?_)
  obtain hg1 := h1.external (by decide) hqm hg
  obtain hy1 := h1.external (by decide) hqm hy
  obtain hr1 := h1.external (by decide) hqm hr
  obtain hs1 := h1.external (by decide) hqm hs
  obtain hz1 := h1.external (by decide) hqm hz
  obtain hm1 := (h1.fields (by decide) hqm .mask).trans hm
  obtain hqm1 := h1.output (by decide) hqm
  refine WP.seq (WP.mono (readyRange_ok h1.ready .q Core.signatureR (by trivial) hr1.active
    (by rw [hrl]; omega_using [hql]) (by simp only [hrl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm1) fun s2 h2 => ?_)
  obtain hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  obtain hy2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy1
  obtain hr2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.signatureR]) hr1
  obtain hs2 := h2.preserve h1.ready (by decide) (by decide) (by trivial) hs1
  obtain hz2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.digest]) hz1
  obtain hqm2 := h2.preserve h1.ready (Nat.le_refl _) (by decide) (by trivial) hqm1
  refine WP.seq (WP.mono (readyRange_ok h2.ready .q Core.signatureS (by trivial) hs2.active
    (by rw [hsl]; omega_using [hql]) (by simp only [hsl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false h2.mask) fun s3 h3 => ?_)
  obtain hg3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg2
  obtain hy3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy2
  obtain hr3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.signatureR]) hr2
  obtain hs3 := h3.preserve h2.ready (by decide) (by decide) (by trivial) hs2
  obtain hz3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.digest]) hz2
  obtain hqm3 := h3.preserve h2.ready (Nat.le_refl _) (by decide) (by trivial) hqm2
  refine WP.seq (WP.mono (coreVerify_ok M h3.ready hp hq hop hoq hpf hqf data hg3 hy3 hr3 hs3 hz3
    hgl hyl hrl hsl hzl hqm3) fun s4 ⟨h4, hu4bytes, hf4, hm4eq, hk4⟩ => ?_)
  obtain hr4 := h3.ready.preserveExternal h4 hf4 hk4 (by decide) (by simp [stablePointer, Core.signatureR]) hr3
  obtain hm4 := hm4eq.trans h3.mask
  obtain hu4 := h4.encodedLocal .q u (data.value L) (by decide) hu hu4bytes
  refine WP.mono (readyEqual_ok h4 (Core.scalar u) Core.signatureR
    (by change u < 2 ^ 16; decide) (by trivial) hu4 hr4.active
    (by simp only [encodeBE_length, ModulusSide.length, hrl])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) false hm4) fun s5 h5 => ?_
  refine ⟨h5.ready, ?_, ((((h1.scheduleFrame (by decide) hqm).trans h2.scheduleFrame).trans h3.scheduleFrame).trans hf4).trans h5.scheduleFrame,
    ((((h1.keep.trans h2.keep).trans h3.keep).trans hk4).trans h5.keep).mono (by decide)⟩
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length, ModulusSide.value] at hm5
  exact hm5

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def prevalidatedBody (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (Prevalidated.compute mul) (.block SignVerify.result)

theorem prevalidatedBody_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues) {qb : List Byte} (h : VerificationOperands L data qb s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (prevalidatedBody M.mm) s0 fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (prevalidatedAccepted L data valid).toNat ∧
      Outside L.base 128 (usedBytes - 128) s0.mem t.mem ∧ Keep coreRegs s0 t := by
  unfold prevalidatedBody
  refine WP.seq (WP.mono (prevalidatedCompute_ok M h0 hp hq hop hoq hpf hqf data h.generator h.publicValue
    h.signatureR h.signatureS h.digest h.generatorLength h.publicLength
    h.rLength h.sLength h.digestBound hm)
    fun s1 ⟨h1, hm1, hf1, hk1⟩ => ?_)
  refine WP.mono (result_ok h1.scratch h1.parent.x0 (by decide) hm1)
    fun t ⟨ha, hmem, hk⟩ => ?_
  exact ⟨ha,
    by rw [hmem]; exact hf1, (hk1.trans hk).mono (by decide)⟩

theorem prevalidatedBody_spec (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (data : VerifyValues) {qb key signature digest : List Byte} {n : Nat}
    (h : VerificationOperands L data qb s0)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hkl : key.length = 3 * L.pLen + L.qLen) (hsl : signature.length = 2 * L.qLen)
    (hk : Spec.Dsa.publicKeyBytes L.pLen L.qLen key = data.key L)
    (hr : signature.take L.qLen = data.signatureR) (hs : signature.drop L.qLen = data.signatureS)
    (hqn : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n)
    (hv : Spec.Dsa.validatePublicKeyBytes L.pLen L.qLen key = true)
    (hm : word s0.mem L.base Field.mask.offset = mask true) :
    WP isa (prevalidatedBody M.mm) s0 fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.verifyBytes L.pLen L.qLen key signature digest).toNat ∧
      Outside L.base 128 (usedBytes - 128) s0.mem t.mem ∧ Keep coreRegs s0 t := by
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  obtain hv' : publicAccepted L data.generator data.publicValue true = true := by
    rw [publicAccepted_spec L data.generator data.publicValue hsize hop hoq]
    simpa only [Spec.Dsa.validatePublicKeyBytes, L.lengths, decide_true, Bool.not_true,
      hkl, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hk,
      VerifyValues.key] using hv
  obtain he : verifyAccepted L data true = prevalidatedAccepted L data true := by
    simp only [verifyAccepted, prevalidatedAccepted, hv']
  rw [verifyBytes_compute L data key signature digest n hsize hop hoq hqf h.rLength hkl hsl hk hr hs hqn hz, he]
  exact prevalidatedBody_ok M h0 hp hq hop hoq hpf hqf data h hm

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.VerifyingVerified`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.VerifyingABIPre`, which this module and modules that import it used -/

section

/-! # Buffer and stack resources for a complete verification call -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem VerifyingABI.pre {s : State} (h : VerifyingABI s) : VerifyingPre h.input s := by
  have hs : Scr s (stackArg s 0) ((stackArg s 1).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 16⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · exact (ofNat_toNat64 _).symm
  · simpa only [Nat.mul_zero, off_zero] using stackWord_read (count := 2) (j := 0) hargs (by decide) (by decide)
  · exact (ofNat_toNat64 _).symm
  · change s.gpr .x7 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x1).isLt) h.keyScratch) h.used
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x5).isLt) h.signatureScratch) h.used
  · exact source_shrink (src_of_region (p := s.gpr .x6) (by rw [h.rd]; simp)
      (Nat.le_of_lt (s.gpr .x7).isLt) h.digestScratch) h.used

def VerifyingABI.call {s : State} (h : VerifyingABI s) : VerifyingCall := ⟨h.input, s, h.pre⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.VerifyingAgreement`, which this module and modules that import it used -/

section

/-! # Only the verifying ABI's declared public observations determine its schedule -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem verifyingLayout_eq {p₁ p₂ : VerifyingInput} {s₁ s₂ : State}
    {hp₁ : s₁.gpr .x2 = BitVec.ofNat 64 p₁.pLen} {hp₂ : s₂.gpr .x2 = BitVec.ofNat 64 p₂.pLen}
    {hq₁ : s₁.gpr .x3 = BitVec.ofNat 64 p₁.qLen} {hq₂ : s₂.gpr .x3 = BitVec.ofNat 64 p₂.qLen}
    (hb : p₁.base = p₂.base) (hp : p₁.pLen = p₂.pLen) (hq : p₁.qLen = p₂.qLen)
    (hd : p₁.digestPointer = p₂.digestPointer) (hdl : p₁.digest.length = p₂.digest.length)
    (hpb : p₁.components.p = p₂.components.p) (hqb : p₁.components.q = p₂.components.q)
    (hdi : s₁.gpr .x0 = s₂.gpr .x0) (hdx : s₁.gpr .x2 = s₂.gpr .x2)
    (h8 : s₁.gpr .x4 = s₂.gpr .x4) (hcx : s₁.gpr .x3 = s₂.gpr .x3) :
    p₁.layout s₁ hp₁ hq₁ = p₂.layout s₂ hp₂ hq₂ := by
  have hac : p₁.accepted = p₂.accepted := by
    unfold VerifyingInput.accepted
    congr 1
  have hprefix : p₁.prefixLength = p₂.prefixLength := by
    unfold VerifyingInput.prefixLength
    rw [hdl, hqb]
  have hfields : verifyFieldValues s₁ p₁.digestPointer
      (BitVec.ofNat 64 p₁.digest.length) (BitVec.ofNat 64 p₁.prefixLength) p₁.accepted =
      verifyFieldValues s₂ p₂.digestPointer
      (BitVec.ofNat 64 p₂.digest.length) (BitVec.ofNat 64 p₂.prefixLength) p₂.accepted := by
    funext f
    cases f <;> simp only [verifyFieldValues, hd, hdl, hprefix, hac, hdi, hdx, h8, hcx]
  unfold VerifyingInput.layout
  congr 1
  · exact congrArg Spec.Dsa.decodeBE hpb
  · exact congrArg Spec.Dsa.decodeBE hqb

theorem verifyingAgreement {s₁ s₂ : State} (h₁ : VerifyingABI s₁) (h₂ : VerifyingABI s₂)
    (hdi : s₁.gpr .x0 = s₂.gpr .x0) (hdx : s₁.gpr .x2 = s₂.gpr .x2)
    (h8 : s₁.gpr .x4 = s₂.gpr .x4) (hcx : s₁.gpr .x3 = s₂.gpr .x3)
    (hsp : s₁.sp = s₂.sp)
    (a0 : s₁.gpr .x6 = s₂.gpr .x6) (a1 : s₁.gpr .x7 = s₂.gpr .x7)
    (a2 : stackArg s₁ 0 = stackArg s₂ 0)
    (hpub : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
      h₂.input.key.take (3 * h₂.input.pLen + h₂.input.qLen)) : VerifyingAgrees h₂.call h₁.call := by
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat hdx
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat hcx
  have hdl : h₁.input.digest.length = h₂.input.digest.length := by
    change (Spec.Rsa.bytesAt _ _ _).length = (Spec.Rsa.bytesAt _ _ _).length
    rw [bytesAt_length, bytesAt_length, a1]
  rw [← hp, ← hq] at hpub
  have hpb : h₁.input.components.p = h₂.input.components.p := by
    have he := prefix_component_eq (offset := 0) (len := h₁.input.pLen) hpub (by omega_using [])
    simp only [List.drop_zero] at he
    change h₁.input.key.take h₁.input.pLen = h₂.input.key.take h₂.input.pLen
    rw [← hp]
    exact he
  have hqb : h₁.input.components.q = h₂.input.components.q := by
    have he := prefix_component_eq (offset := h₁.input.pLen) (len := h₁.input.qLen) hpub (by omega_using [])
    change (h₁.input.key.drop h₁.input.pLen).take h₁.input.qLen = (h₂.input.key.drop h₂.input.pLen).take h₂.input.qLen
    rw [← hp, ← hq]
    exact he
  exact ⟨verifyingLayout_eq a2 hp hq a0 hdl hpb hqb hdi hdx h8 hcx, hpb, hqb, hdl, hsp⟩

theorem verifyingPublicRelated {s₁ s₂ : State} (h₁ : VerifyingABI s₁) (h₂ : VerifyingABI s₂)
    (h : (Spec.Dsa.verifyContract abi).pub s₁ s₂) : Two VerifyingStart s₁ s₂ := by
  sig_pub [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, hcx, h8, _, a0, a1, a2, _⟩ := h
  have hpub := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpub
  exact ⟨h₂.call, ⟨h₁.call, verifyingAgreement h₁ h₂ hdi hdx h8 hcx hsp a0 a1 a2 hb, rfl⟩,
    ⟨h₂.call, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, hsp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.VerifyingABIPost`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.VerifyingReturn`, which this module and modules that import it used -/

section

/-! # Both verifying branches return the packed byte specification -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def VerifyingPost (p : VerifyingInput) (original t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.verifyBytes p.pLen p.qLen p.key p.signature p.digest).toNat ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem verifyingRejected_ok {p : VerifyingInput} {original s : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength s) (ha : p.accepted = false) :
    WP isa (.block [movi .x0 0]) s
      (VerifyingPost p original) := by
  have hparams : ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes p.pLen p.qLen p.key).params :=
    shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
  have hfalse := verifyBytes_invalid_shape (signature := p.signature) (digest := p.digest) hparams
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨hret, hmem⟩, hk⟩ => ?_
  unfold VerifyingPost
  rw [hfalse]
  exact ⟨hret,
    by rw [hmem]; exact hs.frame, (hs.keep.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Verification correctness and ABI preservation against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem verifyStatus_u32 (result : Bool) :
    ((BitVec.ofNat 64 result.toNat).setWidth 32).toNat = if result then 1 else 0 := by
  cases result <;> rfl

end VG.Proof.Dsa.AArch64

end

end

/-! # DSA verifying verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum.AArch64

/-- An ordinary 1024/160 call with disjoint buffers and an empty digest.
The all-zero key is allowed by the contract and is rejected by the program. -/
def verifyingSatState : State where
  gpr r := match r with
    | .x0 => 0x2000 | .x1 => 404 | .x2 => 128 | .x3 => 20
    | .x4 => 0x4000 | .x5 => 40 | .x6 => 0x5000 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10001 then 0x80 else if a = 0x10009 then 8 else 0
  rd := [⟨0x2000, 404⟩, ⟨0x4000, 40⟩, ⟨0x5000, 0⟩, ⟨0x10000, 16⟩]
  wr := [⟨0x8000, 16384⟩]

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.PrevalidatedComputeCT`, which only this module used -/

section

/-! # Constant time of validation and signing/verification together -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedCompute_ct (M : Mont) : RelCT isa (Two (ScheduleState verifyComputeInputs))
    (Prevalidated.compute M.mm) (Two (ScheduleState verifyComputeInputs)) := by
  have h1 := scheduleMinus_ct verifyComputeInputs verifyComputeInputs_stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega_using [this])
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide) (by taint_decide)
  have h2 := scheduleRange_ct verifyComputeInputs verifyComputeInputs_stable .q Core.signatureR
    (fun p => p.layout.qLen) false (by trivial) (by simp [stablePointer, Core.signatureR])
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h3 := scheduleRange_ct verifyComputeInputs verifyComputeInputs_stable .q Core.signatureS
    (fun p => p.layout.qLen) false (by trivial) (by trivial)
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h4 := coreVerifySchedule_ct M verifyComputeInputs verifyComputeInputs_stable
    (by intro p a ha; simp [verifyComputeInputs, ha])
  have h5 := scheduleEqual_ct verifyComputeInputs verifyComputeInputs_stable (Core.scalar u) Core.signatureR
    (fun p => p.layout.qLen) false (by change u < 2 ^ 16; decide) (by trivial) (by trivial)
    (by simp [stablePointer, Core.signatureR]) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega_using [this]) (by taint_decide)
  unfold Prevalidated.compute seqs
  refine RelCT.seq h1 (RelCT.seq (R := Two (ScheduleState verifyComputeInputs)) ?_
    (RelCT.seq (R := Two (ScheduleState verifyComputeInputs)) ?_ (RelCT.seq h4 ?_)))
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, (h.2.1 (Core.signatureR, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h2
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, (h.2.1 (Core.signatureS, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h3
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q u (by decide) (scalar_space (by decide) p),
        (h.2.1 (Core.signatureR, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h5

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.PrevalidatedReadyCT`, which only this module used -/

section

/-! # The public schedule after independent verifying-workspace initialization -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/PrevalidatedBodyCT.lean`, which only this module imported.
section

/-! # Constant time through validation, computation and the ABI return -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedComputeReturn_ok (M : Mont) {p : SchedulePublic} {s : State} (h : VerifyingBodyPre p s) :
    WP isa (Prevalidated.compute M.mm) s (fun t => t.gpr .x0 = p.layout.base) := by
  obtain ⟨hr, ⟨data, qb, ho, _⟩, ⟨valid, hm⟩⟩ := h
  refine WP.mono (prevalidatedCompute_ok M hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits data
    ho.generator ho.publicValue ho.signatureR ho.signatureS ho.digest
    ho.generatorLength ho.publicLength ho.rLength ho.sLength
    ho.digestBound hm) fun _ h => h.1.parent.x0

theorem prevalidatedBody_ct (M : Mont) : RelCT isa (Two VerifyingBodyPre) (prevalidatedBody M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => fun t => t.gpr .x0 = p.layout.base)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule.1) (prevalidatedCompute_ct M)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => prevalidatedComputeReturn_ok M h
  · exact two_map (fun p => p.layout.base) (fun _ _ h => h) result_ct

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedVerifyingCall => VerifyingShaped c.val))
      (seqs [SignVerify.workspaces, Prevalidated.compute M.mm, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq verifyingWorkspaces_ct ?_
  exact (prevalidatedBody_ct M).mono (fun _ _ h => verifyingReady_related h) (fun _ _ h => h)

end VG.Proof.Dsa.AArch64

end

end


/-! # Constant time of the complete verifying entry point -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedMain_ct (M : Mont) : RelCT isa (Two VerifyingStart) (Prevalidated.verify M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq verifyingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : VerifyingCall => c.layout.base) (fun _ _ h => h.x0) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (prevalidatedSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of the AArch64 DSA private-key validator

Two calls with the same pointers, lengths and public key components take
the same path, whatever their private scalars and scratch hold. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

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

theorem privateEntry_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .x4 = B))
    (.block PrevalidatedSign.validateEntry) (fun _ _ => True) :=
  two_taint [.x4] (pins_of (fun B _ => B) (by
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
  pBound := by rw [c.input.components.pLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega_using [this]
  qBound := by rw [c.input.components.qLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega_using [this]
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
  refine ⟨c.pre.scratch.congr he.keep.wr, he.base, he.fields .p (by decide) (by decide),
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
    eval (.zero .x .x3) s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change some (s.gpr .x3 == (0#64)) = _
  rw [hs.branch, ha.accepted]

theorem PrivateShaped.x0 {reference : PrivateCall} {s : State} (h : PrivateShaped reference s) :
    s.gpr .x0 = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.x0.trans (congrArg ExecutionLayout.base ha.layout)

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
  have hr : s.gpr .x0 = c.layout.base := hs.x0
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
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _⟩ := h
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
  obtain ⟨reference, h₁, h₂, hsp⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂, hsp⟩

/-- A range check keeps the subgroup order's bytes. -/
theorem privateRange_ct (a : Operand) (ha : pointerFits a.pointer) (hp : stablePointer a.pointer)
    (hmem : ∀ p, (a, p.layout.qLen) ∈ privateInputs p)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (Core.operand arg argLen a ++
      Core.enter ModulusSide.q.offset)) hc).isSome = true) :
    RelCT isa (Two (PublicKeyPre privateInputs)) (Checks.range qWorkspace a)
      (Two (PublicKeyPre privateInputs)) := by
  have ct := scheduleRange_ct privateInputs (fun p => privateInputs_stable p) .q a
    (fun p => p.layout.qLen) false ha hp (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) hT
  refine two_post ((two_map (fun p => p) (fun p s h => ⟨h.1, (h.1.2.1 _ (hmem p)).active⟩) ct).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro p s ⟨hs, qb, hqb, hql, hqv⟩
  obtain ⟨bs, hbs, hlen⟩ := hs.2.1 _ (hmem p)
  obtain ⟨valid, hm⟩ := hs.2.2
  refine WP.mono (readyRange_ok hs.1 .q a ha hbs.active (by rw [hlen]; exact p.layout.widths.1)
    (by rw [hlen]; exact Nat.le_refl _) false hm) fun t h => ?_
  exact ⟨h.schedule hs (fun a ha => privateInputs_stable p a ha), qb,
    h.preserve hs.1 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb, hql, hqv⟩

/-- y = g^x and whether `g^q = 1`, in one pass: q's bytes are the public
subgroup order's. -/
theorem privatePow_ct (M : Mont) : RelCT isa (Two (PublicKeyPre privateInputs))
    (SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t))
    (Two (ScheduleState privateInputs)) := by
  have hend (p : SchedulePublic) : t + ModulusSide.p.length p.layout ≤ usedBytes := element_space (by decide) p
  have qsrc {p : SchedulePublic} {s : State} (h : PublicKeyPre privateInputs p s) :
      Src s p.layout.base activeBytes (p.layout.fields .q)
        (Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup) := by
    obtain ⟨hs, qb, hqb, hql, hqv⟩ := h
    rw [← hs.1.fields .q (by decide), ← hql, ← hqv, VG.Proof.Dsa.encodeBE_decodeBE]
    exact hqb.active.source
  refine two_post (two_map (fun p : SchedulePublic => (⟨⟨p.layout, p.layout.pLen, p.layout.qLen, p.greater .p,
      p.odd .p, by have := p.layout.widths; omega_using [this], Nat.le_refl _, p.layout.widths.1,
      by have := p.layout.widths; omega_using [this], by decide, hend p⟩,
      Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup, VG.Proof.Dsa.encodeBE_length _ _⟩ :
        SharedPower.ReadySharedPublic t)) (fun p s h => ?_)
    (SharedPower.readySharedPow_ct M t Core.generator Core.privateScalar (by trivial) (by trivial)
      (by simp [stablePointer, Core.generator]) (by simp [stablePointer, Core.privateScalar]) (by decide)
      (by taint_decide))) ?_
  · obtain ⟨ga, hga, hgl⟩ := h.1.2.1 _ (show (Core.generator, p.layout.pLen) ∈ privateInputs p by
      simp [privateInputs])
    obtain ⟨xa, hxa, hxl⟩ := h.1.2.1 _ (show (Core.privateScalar, p.layout.qLen) ∈ privateInputs p by
      simp [privateInputs])
    exact ⟨⟨h.1.1, ga, xa, hga.active, hxa.active, hgl, hxl⟩, qsrc h⟩
  intro p s h
  have hq := qsrc h
  obtain ⟨hs, qb, hqb, hql, hqv⟩ := h
  obtain ⟨ga, hga, hgl⟩ := hs.2.1 _ (show (Core.generator, p.layout.pLen) ∈ privateInputs p by
    simp [privateInputs])
  obtain ⟨xa, hxa, hxl⟩ := hs.2.1 _ (show (Core.privateScalar, p.layout.qLen) ∈ privateInputs p by
    simp [privateInputs])
  obtain ⟨valid, hm⟩ := hs.2.2
  have hq' : Src s p.layout.base activeBytes (word s.mem p.layout.base Field.q.offset)
      (Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup) := by
    rw [hs.1.fields .q (by decide)]; exact hq
  refine WP.mono (SharedPower.readySharedPow_ok M hs.1 (p.greater .p) (p.odd .p) Core.generator
    Core.privateScalar (by trivial) (by trivial) hga.active hxa.active
    hq' ((VG.Proof.Dsa.encodeBE_length _ _).trans hxl.symm)
    (by rw [hgl]; have := p.layout.widths; omega_using [this]) (by rw [hgl])
    (by rw [hxl]; exact p.layout.widths.1) (by rw [hxl]; have := p.layout.widths; omega_using [this])
    t (by decide) (hend p) hm) fun u ⟨v, h2, h2c⟩ => ?_
  have stable := fun a ha => privateInputs_stable p a ha
  exact h2c.schedule (h2.schedule hs (by decide) (hend p) stable) stable

theorem privateBody_ct (M : Mont) : RelCT isa (Two (PublicKeyPre privateInputs))
    (seqs [seqs (Checks.publicPrefix M.mm), Checks.range qWorkspace Core.privateScalar,
      Checks.range qWorkspace Core.nonce,
      SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t),
      Checks.equal (Core.element t) Core.publicValue, .block SignVerify.result])
    (fun _ _ => True) := by
  have h0 := publicPrefix_known_ct M privateInputs (fun p => privateInputs_stable p)
    (by intro p; simp [privateInputs]) (by intro p; simp [privateInputs])
  have h1 := privateRange_ct Core.privateScalar (by simp [pointerFits, Core.privateScalar])
    (by simp [stablePointer, Core.privateScalar]) (by intro p; simp [privateInputs]) (by taint_decide)
  have h2 := privateRange_ct Core.nonce (by simp [pointerFits, Core.nonce])
    (by simp [stablePointer, Core.nonce]) (by intro p; simp [privateInputs]) (by taint_decide)
  have h4 := scheduleEqual_ct privateInputs (fun p => privateInputs_stable p) (Core.element t) Core.publicValue
    (fun p => p.layout.pLen) false
    (by change t < 2 ^ 16; decide) (by simp [pointerFits, Core.publicValue])
    (by simp [stablePointer, Core.element]) (by simp [stablePointer, Core.publicValue]) (by decide)
    (by intro p; have := p.layout.widths; omega_using [this])
    (by intro p; have := p.layout.widths; omega_using [this]) (by taint_decide)
  unfold seqs
  refine RelCT.seq h0 (RelCT.seq h1 (RelCT.seq h2 (RelCT.seq (privatePow_ct M) (RelCT.seq
    (two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .p t (by decide) (element_space (by decide) p),
        (h.2.1 _ (show (Core.publicValue, p.layout.pLen) ∈ privateInputs p by simp [privateInputs])).active⟩) h4)
    ?_))))
  exact two_map (fun p => p.layout.base) (fun _ _ h => h.1.parent.x0) result_ct

theorem privateSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedPrivateCall => PrivateShaped c.val))
      (seqs [SignVerify.workspaces, seqs (Checks.publicPrefix M.mm),
        Checks.range qWorkspace Core.privateScalar, Checks.range qWorkspace Core.nonce,
        SharedPower.pow M.mm Core.generator Core.privateScalar (Core.element t),
        Checks.equal (Core.element t) Core.publicValue, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq privateWorkspaces_ct ?_
  exact (privateBody_ct M).mono (fun _ _ h => privateReady_related h) (fun _ _ h => h)

theorem privateMain_ct (M : Mont) :
    RelCT isa (Two PrivateStart) (PrevalidatedSign.validate M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq privateShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : PrivateCall => c.layout.base) (fun _ _ h => h.x0) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (privateSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ValidateMain`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.ValidateEntry`, which this module and modules that import it used -/

section

/-! # Complete AAPCS64 entry for DSA verification -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem verifyCapture_ok {s0 : State} {B : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (h11 : s0.gpr .x11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block (SignVerify.verifyFields ++ SignVerify.keyPointers)) s0
      (VerifyEntryPost s0 B (s0.gpr .x6) (s0.gpr .x7)) := by
  rw [WP.block_append_iff]
  refine WP.mono (verifyFields_ok hs h11 hZ) fun s3 ⟨hmem3, hk3⟩ => ?_

  have hfields := verifyFieldMem_fields s0.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3) (s0.gpr .x4) (s0.gpr .x6) (s0.gpr .x7)
  rw [← hmem3] at hfields
  have hunused := verifyFieldMem_unused s0.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3) (s0.gpr .x4) (s0.gpr .x6) (s0.gpr .x7)
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s0.mem s3.mem := by rw [hmem3]; exact verifyFieldMem_frame _ _ _ _ _ _ _ _
  have hk123 := hk3
  have h113 : s3.gpr .x11 = B := (hk3.gpr .x11 (by decide)).trans h11
  refine WP.mono (keyPointers_ok (hs.congr hk123.wr) h113 hZ hfields.1 hfields.2.1 hfields.2.2.1)
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hptr := keyPointerMem_fields s3.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x3)
  rw [← hmem4] at hptr
  have hf4 : Outside B 264 32 s3.mem s4.mem := by rw [hmem4]; exact keyPointerMem_frame _ _ _ _ _
  have hsame (f : Field) (hsep : f.offset + 8 ≤ 264 ∨ 296 ≤ f.offset) :
      word s4.mem B f.offset = word s3.mem B f.offset :=
    hf4.word hsep (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  refine ⟨hdi4, (hsame .p (by decide)).trans hfields.1, (hsame .pLen (by decide)).trans hfields.2.1,
    (hsame .qLen (by decide)).trans hfields.2.2.1, (hsame .signature (by decide)).trans hfields.2.2.2.1,
    (hsame .digest (by decide)).trans hfields.2.2.2.2.1, (hsame .digestLen (by decide)).trans hfields.2.2.2.2.2,
    hptr.1, hptr.2.1, hptr.2.2.1, hptr.2.2.2, ?_, ?_, (hk123.trans hk4).mono (by decide)⟩
  · exact ⟨(hsame .out (by decide)).trans hunused.1, (hsame .nonce (by decide)).trans hunused.2⟩
  · exact (hf3.mono (by decide) (by decide)).trans (hf4.mono (by decide) (by decide))

structure ValidateEntryPost (original : State) (B : Addr) (t : State) : Prop where
  base : t.gpr .x0 = B
  fields : ∀ f, f ≠ .mask → f ≠ .digestPrefixLen →
    word t.mem B f.offset = verifyFieldValues original 0 0 0 true f
  frame : Outside B 0 pWorkspace original.mem t.mem
  keep : Keep coreRegs original t

theorem validateEntry_ok {s0 : State} {B : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (h4 : s0.gpr .x4 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block Prevalidated.validateEntry) s0 (ValidateEntryPost s0 B) := by
  unfold Prevalidated.validateEntry
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.x11, .x6, .x7]
    (Q := fun s => s.gpr .x11 = B ∧ s.gpr .x6 = 0 ∧ s.gpr .x7 = 0 ∧ s.mem = s0.mem)
    (by brun [h4]) rfl rfl rfl) fun s1 ⟨⟨h11, h6, h7, hmem⟩, hk⟩ => ?_
  refine WP.mono (verifyCapture_ok (hs.congr hk.wr) h11 hZ) fun t ht => ?_
  have he (r : Reg) (hr : r ∉ [.x11, .x6, .x7]) := hk.gpr r hr
  refine ⟨ht.base, ?_, ?_, (hk.trans ht.keep).mono (by decide)⟩
  · intro f hm hp
    cases f
    case mask => exact False.elim (hm rfl)
    case digestPrefixLen => exact False.elim (hp rfl)
    case p => exact ht.p.trans (he .x0 (by decide))
    case pLen => exact ht.pLen.trans (he .x2 (by decide))
    case qLen => exact ht.qLen.trans (he .x3 (by decide))
    case signature => exact ht.signature.trans (he .x4 (by decide))
    case digest => exact ht.digest.trans h6
    case digestLen => exact ht.digestLen.trans h7
    case out => exact ht.unused.1
    case nonce => exact ht.unused.2
    case q => simpa only [verifyFieldValues, he .x0 (by decide), he .x2 (by decide)] using ht.q
    case g => simpa only [verifyFieldValues, he .x0 (by decide), he .x2 (by decide), he .x3 (by decide)] using ht.g
    case y => simpa only [verifyFieldValues, he .x0 (by decide), he .x2 (by decide), he .x3 (by decide)] using ht.y
    case x => simpa only [verifyFieldValues, he .x0 (by decide), he .x2 (by decide), he .x3 (by decide)] using ht.x
  · rw [← hmem]
    exact ht.frame

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ValidateBody`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.ValidateInitialize`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.ValidateShape`, which only this module used -/

section

/-! # Argument capture and public-domain validation for a complete verifying attempt -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ValidatingPre (p : VerifyingInput) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  pLength : s.gpr .x2 = BitVec.ofNat 64 p.pLen
  qLength : s.gpr .x3 = BitVec.ofNat 64 p.qLen
  base : s.gpr .x4 = p.base
  keySource : Src s p.base usedBytes (s.gpr .x0) p.key
  digestNil : p.digest = []
  digestPointer : p.digestPointer = 0

theorem validatingShape_ok {p : VerifyingInput} {s0 : State} (h : ValidatingPre p s0) :
    WP isa (.seq (.block Prevalidated.validateEntry) Checks.domainShape) s0 (VerifyingShapePost p s0 h.pLength h.qLength) := by
  refine WP.seq (WP.mono (validateEntry_ok h.scratch h.base (by decide)) fun s1 he => ?_)
  have hinside : InScr p.base usedBytes s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  have hkey := h.keySource.congrK hinside he.keep
  have hps : Src s1 p.base usedBytes (s0.gpr .x0) p.components.p := source_take hkey
  have hqs : Src s1 p.base usedBytes (s0.gpr .x0 + BitVec.ofNat 64 p.pLen) p.components.q :=
    source_slice hkey (by rw [p.keyLength]; omega_using [])
  have hp1 : 0 < p.components.p.length := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hq1 : 0 < p.components.q.length := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hp64 : p.components.p.length < 2 ^ 64 := by
    rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  have hq64 : p.components.q.length < 2 ^ 64 := by
    rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  refine WP.mono (domainShape_ok (h.scratch.congr he.keep.wr) he.base (by decide) (he.fields .p (by decide) (by decide))
    (by rw [he.fields .q (by decide) (by decide)]; change _ + s0.gpr .x2 = _; rw [h.pLength])
    (by rw [he.fields .pLen (by decide) (by decide)]; change s0.gpr .x2 = _; rw [h.pLength, p.components.pLength])
    (by rw [he.fields .qLen (by decide) (by decide)]; change s0.gpr .x3 = _; rw [h.qLength, p.components.qLength]) hps hqs hp1 hp64 hq1 hq64 rfl rfl
    p.digestBound (by rw [he.fields .digestLen (by decide) (by decide), h.digestNil]; rfl)) fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  have hall := he.keep.trans hk
  have hft : InScr p.base usedBytes s1.mem s2.mem := by
    apply InScr.of_frm hf
    intro range hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  refine ⟨h.scratch.congr hall.wr, (hk.gpr .x0 (by decide)).trans he.base,
    ?_, hbranch,
    hinside.trans hft,
    hall.mono (by decide)⟩
  intro f
  by_cases hm : f = .mask
  · subst f; exact hmask
  by_cases hp : f = .digestPrefixLen
  · subst f; exact hprefix
  rw [shape_field hf f hp hm, he.fields f hm hp]
  simp only [VerifyingInput.layout, h.digestPointer, h.digestNil, List.length_nil,
    VerifyingInput.prefixLength, Nat.min_eq_left (Nat.zero_le _)]
  cases f <;> simp_all [verifyFieldValues]


end VG.Proof.Dsa.AArch64

end

end

/-! # Establishing all verifying operands after public domain acceptance -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/ValidateOperands.lean`, which only this module imported.
section

/-! # Packed verification operands after workspace initialization -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem validatingOperands {p : VerifyingInput} {original s : State}
    {hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen}
    {hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen} {pi qi : BitVec 64}
    (h : Ready ((p.layout original hp hq).withInverses pi qi) s)
    (hkey : Src s p.base usedBytes (original.gpr .x0) p.key)
 :
    OperandBytes s p.base usedBytes Core.generator p.components.g ∧
    OperandBytes s p.base usedBytes Core.publicValue p.components.y ∧
    OperandBytes s p.base usedBytes ⟨.input .q, .qLen⟩ p.components.q := by
  let L := (p.layout original hp hq).withInverses pi qi
  have hqlen : p.components.q.length = p.qLen := p.components.qLength
  have hglen : p.components.g.length = p.pLen := p.components.gLength
  have hylen : p.components.y.length = p.pLen := p.components.yLength
  have qptr : L.fields .q = original.gpr .x0 + BitVec.ofNat 64 p.pLen := by
    change original.gpr .x0 + original.gpr .x2 = _
    rw [hp]
  have gptr : L.fields .g = original.gpr .x0 + BitVec.ofNat 64 (p.pLen + p.qLen) := by
    change original.gpr .x0 + original.gpr .x2 + original.gpr .x3 = _
    rw [hp, hq, Offset.add_add]
  have yptr : L.fields .y = original.gpr .x0 + BitVec.ofNat 64 (2 * p.pLen + p.qLen) := by
    change original.gpr .x0 + original.gpr .x2 + original.gpr .x3 + original.gpr .x2 = _
    rw [hp, hq, Offset.add_add, Offset.add_add, show p.pLen + (p.qLen + p.pLen) = 2 * p.pLen + p.qLen by omega]
  have hqsrc : Src s p.base usedBytes (L.fields .q) p.components.q := by
    rw [qptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hgsrc : Src s p.base usedBytes (L.fields .g) p.components.g := by
    rw [gptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hysrc : Src s p.base usedBytes (L.fields .y) p.components.y := by
    rw [yptr]; exact source_slice hkey (by rw [p.keyLength]; omega)
  have hpfield : L.fields .pLen = BitVec.ofNat 64 p.pLen := hp
  have hqfield : L.fields .qLen = BitVec.ofNat 64 p.qLen  := hq
  refine ⟨h.inputOperand .g .pLen (by decide) (by decide) hgsrc (by change L.fields .pLen = BitVec.ofNat 64 p.components.g.length; rw [hglen]; exact hpfield),
    h.inputOperand .y .pLen (by decide) (by decide) hysrc (by change L.fields .pLen = BitVec.ofNat 64 p.components.y.length; rw [hylen]; exact hpfield),
    h.inputOperand .q .qLen (by decide) (by decide) hqsrc (by rw [hqlen]; exact hqfield)⟩

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ValidatingInitialized (p : VerifyingInput) (original : State)
    (hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp hq).withInverses pi qi) s ∧
    (OperandBytes s p.base usedBytes Core.generator p.components.g ∧
      OperandBytes s p.base usedBytes Core.publicValue p.components.y ∧
      OperandBytes s p.base usedBytes ⟨.input .q, .qLen⟩ p.components.q) ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    InScr p.base usedBytes original.mem s.mem ∧ Keep coreRegs original s

theorem validatingInitialize_ok {p : VerifyingInput} {original s : State} (h : ValidatingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces s (ValidatingInitialized p original h.pLength h.qLength) := by
  let L := p.layout original h.pLength h.qLength
  have hkey := h.keySource.congrK hs.frame hs.keep
  have hps : Src s L.base usedBytes (L.fields .p) p.components.p := source_take hkey
  have hqs : Src s L.base usedBytes (L.fields .q) p.components.q := by
    change Src s p.base usedBytes (original.gpr .x0 + original.gpr .x2) p.components.q
    rw [h.pLength]
    exact source_slice hkey (by rw [p.keyLength]; omega_using [])
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  refine WP.mono (workspacesReady_ok (L := L) hs.scratch hs.x0 hs.fields hps hqs p.components.pLength p.components.qLength
    rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  have hframe : InScr p.base usedBytes s.mem t.mem := InScr.of_outside hf (by decide)
  have hfull := hs.frame.trans hframe
  have hkeep := hs.keep.trans hk
  refine ⟨pi, qi, hr, validatingOperands hr (h.keySource.congrK hfull hkeep), ?_, hfull, hkeep.mono (by decide)⟩
  · exact hm.trans ((hs.fields .mask).trans (congrArg mask ha))

end VG.Proof.Dsa.AArch64

end

end

/-! # Complete public-key algebraic validation, with the original rejection policy -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ValidatingPost (p : VerifyingInput) (original t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key).toNat ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem validatingBody_ok (M : Mont) {p : VerifyingInput} {original s : State} (h : ValidatingPre p original)
    (hi : ValidatingInitialized p original h.pLength h.qLength s) (ha : p.accepted = true) :
    WP isa (seqs [Checks.publicKey M.mm, .block SignVerify.result]) s (ValidatingPost p original) := by
  obtain ⟨pi, qi, hr, ⟨hg, hy, hqb⟩, hm, hf, hk⟩ := hi
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
  refine WP.seq (WP.mono (publicKey_ok M hr hp hq hpodd hqodd hpf hqf hg hy hqb
    p.components.gLength p.components.yLength p.components.qLength rfl hm)
    fun t ⟨ht, hmask, _, hframe, hkeep⟩ => ?_)
  refine WP.mono (result_ok ht.scratch ht.parent.x0 (by decide) hmask) fun u ⟨hret, hmem, hku⟩ => ?_
  refine ⟨?_, ?_, ((hk.trans hkeep).trans hku).mono (by decide)⟩
  · rw [he]; exact hret
  · rw [hmem]
    exact hf.trans (InScr.of_outside hframe (by decide))

end VG.Proof.Dsa.AArch64

end

end

/-! # Functional correctness of the complete separate DSA public-key validator -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem validatingMain_ok (M : Mont) {p : VerifyingInput} {s0 : State} (h : ValidatingPre p s0) :
    WP isa (Prevalidated.validate M.mm) s0 (ValidatingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (validatingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · change some (s.gpr .x3 == (0#64)) = some true
      simp only [hs.branch, ha, Bool.not_false]
    · have hp := shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
      change ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes p.pLen p.qLen p.key).params at hp
      have hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = false := by
        simp only [Spec.Dsa.validatePublicKeyBytes, p.lengths, decide_true, Bool.not_true,
          p.keyLength, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        simp only [hp, decide_false, Bool.false_and]
      refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s.mem)
        (by brun) rfl rfl rfl) fun t ⟨⟨hret, hmem⟩, hk⟩ => ?_
      exact ⟨by rw [hv]; exact hret, by rw [hmem]; exact hs.frame,
        (hs.keep.trans hk).mono (by decide)⟩
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change some (s.gpr .x3 == (0#64)) = some false
      simp only [hs.branch, ha, Bool.not_true]
    · refine WP.seq (WP.mono (validatingInitialize_ok h hs ha) fun t ht => ?_)
      exact validatingBody_ok M h ht ha

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of the AArch64 DSA domain check

Every input is public: two calls with the same pointers, lengths and domain
bytes take the same path, whatever their scratch holds. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ValidatingCall where
  input : VerifyingInput
  original : State
  pre : ValidatingPre input original

abbrev ValidatingCall.layout (c : ValidatingCall) : ExecutionLayout :=
  c.input.layout c.original c.pre.pLength c.pre.qLength

structure ValidatingAgrees (reference c : ValidatingCall) : Prop where
  layout : c.layout = reference.layout
  key : c.input.key = reference.input.key

def ValidatingStart (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧ c.original = s

def ValidatingEntered (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧
    ValidateEntryPost c.original c.input.base s

def ValidatingShaped (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧
    VerifyingShapePost c.input c.original c.pre.pLength c.pre.qLength s

def ValidatingReady (reference : ValidatingCall) (s : State) : Prop :=
  ∃ c : ValidatingCall, ValidatingAgrees reference c ∧
    ValidatingInitialized c.input c.original c.pre.pLength c.pre.qLength s

theorem ValidatingAgrees.pLen {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.pLen = reference.input.pLen := congrArg ExecutionLayout.pLen h.layout

theorem ValidatingAgrees.qLen {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.qLen = reference.input.qLen := congrArg ExecutionLayout.qLen h.layout

theorem ValidatingAgrees.pb {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.components.p = reference.input.components.p := by
  change c.input.key.take c.input.pLen = reference.input.key.take reference.input.pLen
  rw [h.key, h.pLen]

theorem ValidatingAgrees.qb {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.components.q = reference.input.components.q := by
  change (c.input.key.drop c.input.pLen).take c.input.qLen =
    (reference.input.key.drop reference.input.pLen).take reference.input.qLen
  rw [h.key, h.pLen, h.qLen]

theorem ValidatingAgrees.accepted {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold VerifyingInput.accepted
  congr 1
  · exact h.pb
  · exact h.qb

theorem validateEntry_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .x4 = B))
    (.block Prevalidated.validateEntry) (fun _ _ => True) :=
  two_taint [.x4] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

theorem validatingEntered_ct : RelCT isa (Two ValidatingStart) (.block Prevalidated.validateEntry)
    (Two ValidatingEntered) := by
  refine two_post (two_map (fun c : ValidatingCall => c.layout.base) ?_ validateEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact c.pre.base.trans (congrArg ExecutionLayout.base ha.layout)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (validateEntry_ok c.pre.scratch c.pre.base (by decide)) fun t ht => ⟨c, ha, ht⟩

def ValidatingCall.shape (c : ValidatingCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  digestLen := 0
  extentBound := by decide
  pPositive := by rw [c.input.components.pLength]; have := c.layout.widths; change 0 < c.layout.pLen; omega_using [this]
  qPositive := by rw [c.input.components.qLength]; have := c.layout.widths; change 0 < c.layout.qLen; omega_using [this]
  pBound := by rw [c.input.components.pLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega_using [this]
  qBound := by rw [c.input.components.qLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega_using [this]
  digestBound := by decide

theorem ValidatingAgrees.shape {reference c : ValidatingCall} (h : ValidatingAgrees reference c) :
    c.shape = reference.shape := by
  unfold ValidatingCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pb
  · exact h.qb

theorem ValidatingEntered.context {reference : ValidatingCall} {s : State} (h : ValidatingEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  have hkey := c.pre.keySource.congrK hf he.keep
  have hps : Src s c.input.base usedBytes (c.layout.fields .p) c.input.components.p := source_take hkey
  have hqs : Src s c.input.base usedBytes (c.layout.fields .q) c.input.components.q := by
    change Src s c.input.base usedBytes (c.original.gpr .x0 + c.original.gpr .x2) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega_using [])
  refine ⟨c.pre.scratch.congr he.keep.wr, he.base, he.fields .p (by decide) (by decide),
    he.fields .q (by decide) (by decide), ?_, ?_, he.fields .digestLen (by decide) (by decide), hps, hqs⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.components.p.length
    rw [c.input.components.pLength]
    exact (he.fields .pLen (by decide) (by decide)).trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.components.q.length
    rw [c.input.components.qLength]
    exact (he.fields .qLen (by decide) (by decide)).trans c.pre.qLength

theorem validatingShape_ct : RelCT isa (Two ValidatingStart)
    (.seq (.block Prevalidated.validateEntry) Checks.domainShape) (Two ValidatingShaped) := by
  refine two_post (RelCT.seq validatingEntered_ct
    (two_map ValidatingCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (validatingShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

theorem ValidatingShaped.branch {reference : ValidatingCall} {s : State} (h : ValidatingShaped reference s) :
    eval (.zero .x .x3) s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change some (s.gpr .x3 == (0#64)) = _
  rw [hs.branch, ha.accepted]

theorem ValidatingShaped.x0 {reference : ValidatingCall} {s : State} (h : ValidatingShaped reference s) :
    s.gpr .x0 = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.x0.trans (congrArg ExecutionLayout.base ha.layout)

def ValidatingCall.initialization (c : ValidatingCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  pLength := c.input.components.pLength
  qLength := c.input.components.qLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem ValidatingShaped.initialization {reference : ValidatingCall} {s : State}
    (h : ValidatingShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .x0 = c.layout.base := hs.x0
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hkey := c.pre.keySource.congrK hs.frame hs.keep
  have hps' : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.components.p := source_take hkey
  have hqs' : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.components.q := by
    change Src s c.input.base usedBytes (c.original.gpr .x0 + c.original.gpr .x2) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega_using [])
  rw [hag.layout] at hf hr hscr hps' hqs'
  rw [hag.pb] at hps'
  rw [hag.qb] at hqs'
  exact ⟨hscr, hr, hf, hps', hqs'⟩

abbrev AcceptedValidatingCall := {c : ValidatingCall // c.input.accepted = true}

theorem validatingWorkspaces_ct : RelCT isa (Two (fun c : AcceptedValidatingCall => ValidatingShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedValidatingCall => ValidatingReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedValidatingCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (validatingInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

/-- The domain's operands, as the schedule reads them. -/
def validatingInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.publicValue, p.layout.pLen), (⟨.input .q, .qLen⟩, p.layout.qLen), (Core.generator, p.layout.pLen)]

theorem validatingInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ validatingInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · simp [Core.generator, stablePointer]

def ValidatingCall.schedule (c : ValidatingCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
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

theorem ValidatingReady.body {reference : ValidatingCall} {s : State} (ha : reference.input.accepted = true)
    (h : ValidatingReady reference s) : ∃ pi qi, PublicKeyPre validatingInputs (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change (OperandBytes s c.layout.base usedBytes Core.generator c.input.components.g ∧
    OperandBytes s c.layout.base usedBytes Core.publicValue c.input.components.y ∧
    OperandBytes s c.layout.base usedBytes ⟨.input .q, .qLen⟩ c.input.components.q) at ho
  rw [hag.layout] at hr ho hmask
  have hgl : c.input.components.g.length = reference.layout.pLen := c.input.components.gLength.trans hag.pLen
  have hyl : c.input.components.y.length = reference.layout.pLen := c.input.components.yLength.trans hag.pLen
  have hql : c.input.components.q.length = reference.layout.qLen := c.input.components.qLength.trans hag.qLen
  refine ⟨pi, qi, ⟨hr, ?_, ⟨true, hmask⟩⟩, c.input.components.q, ho.2.2, hql, ?_⟩
  · intro a ha
    simp only [validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨_, ho.2.1, hyl⟩
    · exact ⟨_, ho.2.2, hql⟩
    · exact ⟨_, ho.1, hgl⟩
  · change Spec.Dsa.decodeBE c.input.components.q = Spec.Dsa.decodeBE reference.input.components.q
    rw [hag.qb]

theorem validatingReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedValidatingCall => ValidatingReady c.val) s₁ s₂) :
    Two (PublicKeyPre validatingInputs) s₁ s₂ := by
  obtain ⟨reference, h₁, h₂, hsp⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂, hsp⟩

theorem validatingBody_ct (M : Mont) : RelCT isa (Two (PublicKeyPre validatingInputs))
    (seqs [Checks.publicKey M.mm, .block SignVerify.result]) (fun _ _ => True) := by
  have h1 := publicKey_ct M validatingInputs (fun p => validatingInputs_stable p)
    (by intro p; simp [validatingInputs]) (by intro p; simp [validatingInputs])
    (by intro p; simp [validatingInputs])
  unfold seqs
  refine RelCT.seq h1 ?_
  exact two_map (fun p => p.layout.base) (fun _ _ h => h.1.parent.x0) result_ct

theorem validatingSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedValidatingCall => ValidatingShaped c.val))
      (seqs [SignVerify.workspaces, Checks.publicKey M.mm, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq validatingWorkspaces_ct ?_
  exact (validatingBody_ct M).mono (fun _ _ h => validatingReady_related h) (fun _ _ h => h)

theorem validatingMain_ct (M : Mont) :
    RelCT isa (Two ValidatingStart) (Prevalidated.validate M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq validatingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : ValidatingCall => c.layout.base) (fun _ _ h => h.x0) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (validatingSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64
