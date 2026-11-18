module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Spec.Dsa.DomainChecked
-- Proofs inside exposed definitions (structure values) use these: Lean needs them public.
public import VerifiedGarbage.Proof.Bignum.Octets -- shake: keep
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Sha256.Stream
-- Proofs inside exposed definitions (structure values) use these: Lean needs them public.
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Derive
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
public import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Derive
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
import VerifiedGarbage.Proof.Dsa.X86_64.PublicCalls
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.SigningShape
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
meta import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicCalls
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningShape
meta import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
meta import VerifiedGarbage.Proof.Dsa.X86_64.Result
meta import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.Derive
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
meta import VerifiedGarbage.Proof.Dsa.Layout

/-! ### `Dsa.X86_64.DeriveCheckedCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.DeriveMainCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.DeriveCT`, which this module and modules that import it used -/

section

/-! # Constant time of x86-64 DSA key derivation

x is secret: two calls with the same pointers, lengths and domain take the
same path. Its range check, g^x and the signer's checks run on the signer's
schedule, whose operands' bytes may differ; the copies move secret bytes at
public addresses. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-! ## The entry and the domain's shape -/

theorem deriveEntry_ct : RelCT isa (Two (EntryStart 2)) (.block Generate.deriveEntry) (fun _ _ => True) := by
  change RelCT isa (Two (EntryStart 2)) (.block (([.mov .r11 (.mem (Crt.stk 2))] : List Instr) ++
    (SignVerify.save ++ deriveFields ++ SignVerify.keyPointers ++
      [.store (SignVerify.initial .x) .r9, .mov .rax (.reg .r11),
        .alu .add .rax (.imm (BitVec.ofNat 32 derivedY)), .store (SignVerify.initial .y) .rax]))) _
  apply RelCT.block_append
  exact RelCT.seq (entryScratch_ct 2 (by taint_decide)) (two_taint [.r11, .rsp] pins_entryPtrs (by taint_decide))

structure DeriveCall where
  input : DeriveInput
  original : State
  pre : DerivePre input original

abbrev DeriveCall.layout (c : DeriveCall) : ExecutionLayout := c.input.layout c.original c.pre.pLength

structure DeriveAgrees (reference c : DeriveCall) : Prop where
  layout : c.layout = reference.layout
  params : c.input.params = reference.input.params
  stack : c.original.gpr .rsp = reference.original.gpr .rsp

def DeriveStart (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧ c.original = s

def DeriveEntered (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧
    KeygenEntryPost c.original c.input.base (deriveFieldValues c.original (BitVec.ofNat 64 c.input.qLen)
      c.input.base true) s

def DeriveShaped (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧ DeriveShapePost c.input c.original c.pre.pLength s

theorem DeriveAgrees.pLen {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.pLen = reference.input.pLen := congrArg ExecutionLayout.pLen h.layout

theorem DeriveAgrees.qLen {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.qLen = reference.input.qLen := congrArg ExecutionLayout.qLen h.layout

theorem DeriveAgrees.pb {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.pb = reference.input.pb := by
  rw [ParametersInput.pb, ParametersInput.pb, h.params, h.pLen]

theorem DeriveAgrees.qb {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.qb = reference.input.qb := by
  rw [ParametersInput.qb, ParametersInput.qb, h.params, h.pLen, h.qLen]

theorem DeriveAgrees.accepted {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold ParametersInput.accepted
  congr 1
  · exact h.pb
  · exact h.qb

theorem DeriveAgrees.base {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.base = reference.input.base := congrArg ExecutionLayout.base h.layout

theorem deriveEntered_ct : RelCT isa (Two DeriveStart) (.block Generate.deriveEntry) (Two DeriveEntered) := by
  refine two_post (two_map (fun c : DeriveCall => (c.layout.base, c.original.gpr .rsp)) ?_ deriveEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    refine ⟨ha.stack, ?_, ?_⟩
    · rw [← ha.stack]
      exact c.pre.base.trans ha.base
    · rw [← ha.stack]
      exact c.pre.stackRead 2 (by decide) (by decide)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (deriveEntry_ok (scratch_prefix c.pre.scratch (by decide) (by decide)) rfl
      c.pre.stackRead c.pre.stackSeparate c.pre.qLength c.pre.base) fun t ht => ⟨c, ha, ht⟩

def DeriveCall.shape (c : DeriveCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.pb
  qBytes := c.input.qb
  digestLen := 0
  extentBound := by decide
  pPositive := c.input.pPositive
  qPositive := c.input.qPositive
  pBound := by rw [c.input.pbLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega_using [this]
  qBound := by rw [c.input.qbLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega_using [this]
  digestBound := by decide

theorem DeriveAgrees.shape {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.shape = reference.shape := by
  unfold DeriveCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pb
  · exact h.qb

theorem DeriveEntered.context {reference : DeriveCall} {s : State} (h : DeriveEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base deriveExtent c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _, _⟩ := c.pre.sources hf (he.keep.mono (by decide))
  have hu : usedBytes ≤ deriveExtent := by decide
  refine ⟨scratch_prefix (n := usedBytes) (c.pre.scratch.congr he.keep.2.2) hu (by decide), he.base,
    he.fields .p (by decide) (by decide), he.fields .q (by decide) (by decide), ?_, ?_,
    he.fields .digestLen (by decide) (by decide), source_shrink hps hu, source_shrink hqs hu⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.pb.length
    rw [c.input.pbLength]
    exact (he.fields .pLen (by decide) (by decide)).trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.qb.length
    rw [c.input.qbLength]
    exact he.fields .qLen (by decide) (by decide)

theorem deriveShape_ct : RelCT isa (Two DeriveStart)
    (.seq (.block Generate.deriveEntry) Checks.domainShape) (Two DeriveShaped) := by
  refine two_post (RelCT.seq deriveEntered_ct
    (two_map DeriveCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (deriveShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

theorem DeriveShaped.branch {reference : DeriveCall} {s : State} (h : DeriveShaped reference s) :
    eval .e s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change s.zf = _
  rw [hs.branch, ha.accepted]

/-! ## A malformed domain -/

structure DeriveFailurePublic where
  base : Addr
  output : Addr
  width : Nat

def DeriveFailurePre (p : DeriveFailurePublic) (s : State) : Prop :=
  s.gpr .rdi = p.base ∧ ∃ pLen qLen : Nat, p.width = 3 * pLen + 2 * qLen ∧
    Scr s p.base pWorkspace ∧ word s.mem p.base Field.out.offset = p.output ∧
    word s.mem p.base Field.pLen.offset = BitVec.ofNat 64 pLen ∧
    word s.mem p.base Field.qLen.offset = BitVec.ofNat 64 qLen

def DeriveFailureRegs (p : DeriveFailurePublic) (s : State) : Prop :=
  s.gpr .rdi = p.base ∧ s.gpr .rsi = p.output ∧ s.gpr .rcx = BitVec.ofNat 64 p.width

theorem deriveFailure_ct : RelCT isa (Two DeriveFailurePre) Generate.deriveFailure (fun _ _ => True) := by
  unfold Generate.deriveFailure seqs
  refine RelCT.seq (two_piece (Ψ := DeriveFailureRegs) [.rdi]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact h.1)) (by taint_decide) ?_) ?_
  · intro p s ⟨hdi, pl, ql, hw, hs, ho, hp, hq⟩
    refine WP.mono (WP.keep [.rax, .rsi, .rcx] (Q := fun t =>
      t.gpr .rsi = p.output ∧ t.gpr .rcx = BitVec.ofNat 64 p.width) ?_ rfl)
      fun t ⟨⟨hsi, hcx⟩, hk⟩ => ⟨(hk.gpr (by decide)).trans hdi, hsi, hcx⟩
    xrun [State.ea, Core.field, fieldAddress, hdi, ho, hp, hq,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 (Nat.le_refl _)),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .pLen).2 (Nat.le_refl _)),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 (Nat.le_refl _))]
    simp only [BitVec.ofNat_add_ofNat, hw]
    congr 1
    omega_using []
  · exact two_taint [.rdi, .rsi, .rcx]
      (pins_of (fun p r => if r = .rdi then p.base else if r = .rsi then p.output else BitVec.ofNat 64 p.width)
        (by
          intro p s h r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2)) (by taint_decide)

def DeriveCall.failure (c : DeriveCall) : DeriveFailurePublic where
  base := c.layout.base
  output := c.layout.fields .out
  width := c.input.outLen

theorem DeriveShaped.failure {reference : DeriveCall} {s : State} (h : DeriveShaped reference s) :
    DeriveFailurePre reference.failure s := by
  obtain ⟨c, ha, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hscr : Scr s c.layout.base pWorkspace := scratch_prefix hs.scratch (by decide) (by decide)
  have hw : reference.input.outLen = 3 * reference.layout.pLen + 2 * reference.layout.qLen := rfl
  rw [ha.layout] at hf hr hscr
  exact ⟨hr, reference.layout.pLen, reference.layout.qLen, hw, hscr, hf .out,
    (hf .pLen).trans reference.layout.pLength, (hf .qLen).trans reference.layout.qLength⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.DeriveBodyCT`, which this module and modules that import it used -/

section

/-! # Constant time of derivation's computation: x's range, g^x, y's copy and the key checks

The operands' bytes may differ between two calls, x's among them: the
schedule relates two runs by their public layout alone. The subgroup order's
bytes are kept exactly, at derivation's extent, for the key checks. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Derivation's operands: y's slot, q, g and x. -/
def deriveInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.publicValue, p.layout.pLen), (⟨.input .q, .qLen⟩, p.layout.qLen), (Core.generator, p.layout.pLen),
    (Core.privateScalar, p.layout.qLen)]

theorem deriveInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ deriveInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [deriveInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · simp [Core.generator, stablePointer]
  · simp [Core.privateScalar, stablePointer]

/-- An operand past the signer's layout stays available, with whatever bytes
it then holds, when its pointer and length do. -/
theorem ExternalAvailable.rebuild {L : ExecutionLayout} {a : Operand} {n : Nat} {s t : State}
    (hs : Ready L s) (ht : Ready L t) (hk : Keep coreRegs s t)
    (ha : a.length ≠ .mask) (hp : stablePointer a.pointer)
    (h : ExternalAvailable L a n s) : ExternalAvailable L a n t := by
  obtain ⟨bs, hb, hl⟩ := h
  have hptr := hs.pointer_eq ht a.pointer hp
  refine ⟨Spec.Rsa.bytesAt t.mem (pointerValue t.mem L.base a.pointer) n, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [bytesAt_length]
    exact (ht.fields a.length ha).trans ((hs.fields a.length ha).symm.trans (hl ▸ hb.length))
  · intro i hi
    rw [bytesAt_length] at hi
    rw [hk.2.1, hk.2.2, hptr]
    exact hb.source.rd i (by omega_using [hl, hi])
  · intro i hi
    simp [Spec.Rsa.bytesAt]
  · intro i hi
    rw [bytesAt_length] at hi
    rw [hptr]
    exact hb.source.out i (by omega_using [hl, hi])
  · exact bytesAt_length _ _ _

/-- The schedule's state, with derivation's extent and q's bytes. -/
def DeriveSched (p : SchedulePublic) (s : State) : Prop :=
  ScheduleState deriveInputs p s ∧ Scr s p.layout.base deriveExtent ∧
  ∃ qb : List Byte, OperandBytes s p.layout.base deriveExtent ⟨.input .q, .qLen⟩ qb ∧
    qb.length = p.layout.qLen ∧ Spec.Dsa.decodeBE qb = p.layout.subgroup

theorem deriveRange_ct : RelCT isa (Two DeriveSched) (Checks.range qWorkspace Core.privateScalar)
    (Two DeriveSched) := by
  have ct := scheduleRange_ct deriveInputs (fun p => deriveInputs_stable p) .q Core.privateScalar
    (fun p => p.layout.qLen) false (by trivial) (by simp [stablePointer, Core.privateScalar])
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  refine two_post ((two_map (fun p => p) (fun p s h => ⟨h.1, (h.1.2.1 (Core.privateScalar, p.layout.qLen)
    (by simp [deriveInputs])).active⟩)
    ct).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro p s ⟨hs, hscr, qb, hqb, hql, hqv⟩
  obtain ⟨bs, hbs, hlen⟩ := hs.2.1 _ (show (Core.privateScalar, p.layout.qLen) ∈ deriveInputs p by
    simp [deriveInputs])
  obtain ⟨valid, hm⟩ := hs.2.2
  refine WP.mono (readyRange_ok hs.1 .q Core.privateScalar (by trivial) hbs.active
    (by rw [hlen]; exact p.layout.widths.1) (by rw [hlen]; exact Nat.le_refl _) false hm) fun t h => ?_
  exact ⟨h.schedule hs (fun a ha => deriveInputs_stable p a ha), hscr.congr h.keep.2.2,
    qb, h.preserve hs.1 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb, hql, hqv⟩

theorem derivePow_ct (M : Mont) (Sq : MontS) : RelCT isa (Two DeriveSched)
    (Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2)) (Two DeriveSched) := by
  have hend (p : SchedulePublic) : t2 + ModulusSide.p.length p.layout ≤ usedBytes := element_space (by decide) p
  have ct := schedulePow_ct M Sq deriveInputs (fun p => deriveInputs_stable p) .p t2 Core.generator
    Core.privateScalar (fun p => p.layout.pLen) (fun p => p.layout.qLen) (by trivial) (by trivial)
    (by simp [stablePointer, Core.generator]) (by simp [stablePointer, Core.privateScalar])
    (by intro p; have := p.layout.widths; omega_using [this]) (fun _ => Nat.le_refl _)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega_using [this])
    (by decide) (by decide) hend (by taint_decide)
  refine two_post ((two_map (fun p => p) (fun p s h => ⟨h.1,
    (h.1.2.1 (Core.generator, p.layout.pLen) (by simp [deriveInputs])).active,
    (h.1.2.1 (Core.privateScalar, p.layout.qLen) (by simp [deriveInputs])).active⟩) ct).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro p s ⟨hs, hscr, qb, hqb, hql, hqv⟩
  obtain ⟨ga, hga, hgl⟩ := hs.2.1 _ (show (Core.generator, p.layout.pLen) ∈ deriveInputs p by
    simp [deriveInputs])
  obtain ⟨xa, hxa, hxl⟩ := hs.2.1 _ (show (Core.privateScalar, p.layout.qLen) ∈ deriveInputs p by
    simp [deriveInputs])
  have step := readyPow_ok M Sq hs.1 .p (p.greater .p) (p.odd .p) Core.generator Core.privateScalar
    (by trivial) (by trivial) hga.active hxa.active (by rw [hgl]; have := p.layout.widths; omega)
    (by rw [hgl]; exact Nat.le_refl _) (by rw [hxl]; exact p.layout.widths.1)
    (by rw [hxl]; have := p.layout.widths; omega) t2 (by decide) (hend p)
  refine WP.mono (by simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField] using step)
    fun t h => ?_
  have hf : Outside p.layout.base 128 (deriveExtent - 128) s.mem t.mem :=
    (h.scheduleFrame (by decide) (hend p)).mono (by decide) (by decide)
  exact ⟨h.schedule hs (by decide) (hend p) (fun a ha => deriveInputs_stable p a ha), hscr.congr h.keep.2.2,
    qb, hqb.frame hs.1 h.ready hf h.keep (by decide) (by change Field.q ≠ .mask; decide), hql, hqv⟩

def CopyRegs (p : SchedulePublic) (s : State) : Prop :=
  s.gpr .rsi = off p.layout.base t2 ∧ s.gpr .rdx = off p.layout.base derivedY ∧
    s.gpr .rcx = BitVec.ofNat 64 p.layout.pLen

theorem deriveCopy_ct : RelCT isa (Two DeriveSched) Generate.copyY (Two DeriveSched) := by
  have ct : RelCT isa (Two DeriveSched) Generate.copyY (fun _ _ => True) := by
    unfold Generate.copyY seqs
    refine RelCT.seq (two_piece (Ψ := CopyRegs) [.rdi]
      (pins_of (fun p _ => p.layout.base) (by
        intro p s h r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact h.1.1.parent.rdi)) (by taint_decide) ?_) ?_
    · intro p s h
      exact WP.mono (copyHead_ok h.1.1) fun t ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩
    · exact two_taint [.rsi, .rdx, .rcx]
        (pins_of (fun p r => if r = .rsi then off p.layout.base t2 else if r = .rdx then off p.layout.base derivedY
            else BitVec.ofNat 64 p.layout.pLen)
          (by
            intro p s h r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact h.1
            · exact h.2.1
            · exact h.2.2)) (by taint_decide)
  refine two_post ct ?_
  intro p s ⟨hs, hscr, qb, hqb, hql, hqv⟩
  refine WP.mono (copyY_ok hs.1 hscr) fun t ⟨ht, _, hf, hk⟩ => ?_
  have hp384 : p.layout.pLen ≤ 384 := p.layout.widths.2.2.2
  have hf' : Outside p.layout.base 128 (deriveExtent - 128) s.mem t.mem :=
    hf.mono (by decide) (by unfold deriveExtent; omega_using [hp384])
  obtain ⟨valid, hm⟩ := hs.2.2
  refine ⟨⟨ht, fun a ha => (hs.2.1 a ha).rebuild hs.1 ht hk (deriveInputs_stable p a ha).1
    (deriveInputs_stable p a ha).2, valid, (hf.word (Or.inl (by decide)) (by decide)).trans hm⟩,
    hscr.congr hk.2.2, qb, hqb.frame hs.1 ht hf' hk (by decide) (by change Field.q ≠ .mask; decide), hql, hqv⟩

theorem deriveBodySched_ct (M : Mont) (Sq : MontS) : RelCT isa (Two DeriveSched)
    (seqs [Checks.range qWorkspace Core.privateScalar,
      Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, Checks.signingKey Sq.mm M.mm]) (fun _ _ => True) := by
  have h4 := signingKey_ct M Sq deriveInputs (fun p => deriveInputs_stable p)
    (by intro p; simp [deriveInputs]) (by intro p; simp [deriveInputs]) (by intro p; simp [deriveInputs])
  unfold seqs
  refine RelCT.seq deriveRange_ct (RelCT.seq (derivePow_ct M Sq) (RelCT.seq deriveCopy_ct ?_))
  refine (two_map (Φ := DeriveSched) (fun p => p) (fun p s h => ⟨h.1, ?_⟩) h4).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  obtain ⟨qb, hqb, hql, hqv⟩ := h.2.2
  exact ⟨qb, hqb.shrink (by decide), hql, hqv⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of the complete x86-64 key derivation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-! ## Writing the key at public addresses -/

structure KeyPublic where
  base : Addr
  out : Addr
  params : Addr
  publicValue : Addr
  scalar : Addr
  pLen : Nat
  qLen : Nat

def KeyPre (k : KeyPublic) (s : State) : Prop :=
  s.gpr .rdi = k.base ∧ Scr s k.base pWorkspace ∧
  (∃ valid, KeyFields s k.base k.out k.params k.publicValue k.scalar k.pLen k.qLen valid) ∧
  0 < k.pLen ∧ 0 < k.qLen ∧ 3 * k.pLen + 2 * k.qLen < 2 ^ 64 ∧
  KeySource s k.params k.out (2 * k.pLen + k.qLen) (3 * k.pLen + 2 * k.qLen) ∧
  KeySource s k.publicValue k.out k.pLen (3 * k.pLen + 2 * k.qLen) ∧
  KeySource s k.scalar k.out k.qLen (3 * k.pLen + 2 * k.qLen) ∧
  (∀ i < 3 * k.pLen + 2 * k.qLen, InRegions s.wr (k.out + BitVec.ofNat 64 i) 1)

def KeyHeadRegs (k : KeyPublic) (s : State) : Prop :=
  s.gpr .rdi = k.base ∧ s.gpr .rsi = k.params ∧ s.gpr .rdx = k.out ∧
  s.gpr .rcx = BitVec.ofNat 64 (2 * k.pLen + k.qLen) ∧
  KeyRegs s k.out k.publicValue k.scalar k.pLen k.qLen

theorem writeKey_ct : RelCT isa (Two KeyPre) Generate.writeKey
    (Two (fun (k : KeyPublic) (s : State) => s.gpr .rdi = k.base)) := by
  have ct : RelCT isa (Two KeyPre) Generate.writeKey (fun _ _ => True) := by
    unfold Generate.writeKey seqs
    refine RelCT.seq (two_piece (Ψ := KeyHeadRegs) [.rdi]
      (pins_of (fun (k : KeyPublic) _ => k.base) (by
        intro k s h r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact h.1)) (by taint_decide) ?_) ?_
    · intro k s ⟨hdi, hs, ⟨valid, hf⟩, _⟩
      exact WP.mono (keyHead_ok hs hdi (Nat.le_refl _) hf) fun t ⟨h1, h2, h3, _, _, hk, hr⟩ =>
        ⟨(hk.gpr (by decide)).trans hdi, h1, h2, h3, hr⟩
    · exact two_taint [.rdi, .rsi, .rdx, .rcx, .r9, .r10, .r11, .r12, .r13]
        (pins_of (fun k r => match r with
            | .rdi => k.base | .rsi => k.params | .rdx => k.out
            | .rcx => BitVec.ofNat 64 (2 * k.pLen + k.qLen) | .r9 => k.publicValue | .r10 => k.scalar
            | .r11 => BitVec.ofNat 64 k.pLen | .r12 => BitVec.ofNat 64 k.qLen | _ => k.out)
          (by
            intro k s h r hr
            obtain ⟨h1, h2, h3, h4, h5⟩ := h
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact h1
            · exact h2
            · exact h3
            · exact h4
            · exact h5.publicValue
            · exact h5.scalar
            · exact h5.pLen
            · exact h5.qLen
            · exact h5.out)) (by taint_decide)
  refine two_post ct ?_
  intro k s ⟨hdi, hs, ⟨valid, hf⟩, hp, hq, hk, hP, hY, hX, hw⟩
  exact WP.mono (writeKey_ok hs hdi (Nat.le_refl _) hf hp hq hk hP hY hX hw)
    fun t ⟨_, _, _, _, hkt⟩ => (hkt.gpr (by decide)).trans hdi

/-! ## Two calls through the computation -/

def DeriveCall.schedule (c : DeriveCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := 0
  pGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).1
  qGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).2.1
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2
  pFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.pb
    rw [c.input.pbLength] at h
    exact Nat.le_of_lt h
  qFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.qb
    rw [c.input.qbLength] at h
    exact Nat.le_of_lt h
  digestBound := by decide

def DeriveCall.initialization (c : DeriveCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.pb
  qBytes := c.input.qb
  pLength := c.input.pbLength
  qLength := c.input.qbLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem DeriveShaped.initialization {reference : DeriveCall} {s : State}
    (h : DeriveShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hscr : Scr s c.layout.base usedBytes := scratch_prefix (n := usedBytes) hs.scratch (by decide) (by decide)
  obtain ⟨hps, hqs, _, _⟩ := c.pre.sources hs.frame hs.keep
  have hps' : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.pb := source_shrink hps (by decide)
  have hqs' : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.qb := source_shrink hqs (by decide)
  rw [hag.layout] at hf hr hscr hps' hqs'
  rw [hag.pb] at hps'
  rw [hag.qb] at hqs'
  exact ⟨hscr, hr, hf, hps', hqs'⟩

abbrev AcceptedDeriveCall := {c : DeriveCall // c.input.accepted = true}

def DeriveReady (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧ DeriveInitialized c.input c.original c.pre.pLength s

theorem deriveWorkspaces_ct : RelCT isa (Two (fun c : AcceptedDeriveCall => DeriveShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedDeriveCall => DeriveReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedDeriveCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (deriveInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

theorem DeriveReady.sched {reference : DeriveCall} {s : State} (ha : reference.input.accepted = true)
    (h : DeriveReady reference s) : ∃ pi qi, DeriveSched (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, hframe, hk⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  have hscr : Scr s c.layout.base deriveExtent := c.pre.scratch.congr hk.2.2
  change Ready (c.layout.withInverses pi qi) s at hr
  change DeriveOperands (c.layout.withInverses pi qi) c.input s at ho
  have hy : Ready (c.layout.withInverses pi qi) s := hr
  rw [hag.layout] at hr ho hmask hscr
  have hgl : c.input.gb.length = reference.layout.pLen := c.input.gbLength.trans hag.pLen
  have hql : c.input.qb.length = reference.layout.qLen := c.input.qbLength.trans hag.qLen
  have hxl : c.input.x.length = reference.layout.qLen := c.input.xLength.trans hag.qLen
  have hp384 : reference.layout.pLen ≤ 384 := reference.layout.widths.2.2.2
  refine ⟨pi, qi, ⟨hr, ?_, ⟨true, hmask⟩⟩, hscr, c.input.qb, ho.subgroup, hql, ?_⟩
  · intro a ha
    simp only [deriveInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · -- y's slot, past the signer's layout
      have hyw : word s.mem reference.layout.base Field.y.offset = off reference.layout.base derivedY :=
        hr.fields .y (by decide)
      refine ⟨Spec.Rsa.bytesAt s.mem (off reference.layout.base derivedY) reference.layout.pLen,
        ⟨?_, ?_, ?_, ?_⟩, bytesAt_length _ _ _⟩
      · rw [bytesAt_length]
        exact (hr.fields .pLen (by decide)).trans reference.layout.pLength
      · intro i hi
        rw [bytesAt_length] at hi
        show InRegions (s.rd ++ s.wr) (word s.mem reference.layout.base Field.y.offset + BitVec.ofNat 64 i) 1
        rw [hyw, off_add]
        exact scr_byte_rd hscr (by unfold deriveExtent; omega_using [hp384, hi])
      · intro i hi
        show s.mem (word s.mem reference.layout.base Field.y.offset + BitVec.ofNat 64 i) = _
        rw [hyw]
        simp [Spec.Rsa.bytesAt]
      · intro i hi
        rw [bytesAt_length] at hi
        show usedBytes ≤ ofs reference.layout.base (word s.mem reference.layout.base Field.y.offset + BitVec.ofNat 64 i)
        rw [hyw, ofs_off _ (by have := hscr.nowrap; unfold deriveExtent at this; omega_using [hp384, hi, this])]
        exact Nat.le_add_right _ _
    · exact ⟨_, ho.subgroup.shrink (by decide), hql⟩
    · exact ⟨_, ho.generator.shrink (by decide), hgl⟩
    · exact ⟨_, ho.scalar.shrink (by decide), hxl⟩
  · change Spec.Dsa.decodeBE c.input.qb = Spec.Dsa.decodeBE reference.input.qb
    rw [hag.qb]

theorem deriveReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedDeriveCall => DeriveReady c.val) s₁ s₂) : Two DeriveSched s₁ s₂ := by
  obtain ⟨reference, h₁, h₂⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.sched reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.sched reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂⟩

/-- After the computation: what writing the key needs. -/
def DeriveComputed (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧ ∃ pi qi valid,
    Ready (c.layout.withInverses pi qi) s ∧ word s.mem c.input.base Field.mask.offset = mask valid ∧
    InScr c.input.base deriveExtent c.original.mem s.mem ∧ Keep coreRegs c.original s

def DeriveCall.key (c : DeriveCall) : KeyPublic where
  base := c.layout.base
  out := c.layout.fields .out
  params := c.layout.fields .p
  publicValue := c.layout.fields .y
  scalar := c.layout.fields .x
  pLen := c.layout.pLen
  qLen := c.layout.qLen

theorem DeriveComputed.key {reference : DeriveCall} {s : State} (h : DeriveComputed reference s) :
    KeyPre reference.key s := by
  obtain ⟨c, hag, pi, qi, valid, hr, hm, hframe, hk⟩ := h
  have hkey : c.key = reference.key := by unfold DeriveCall.key; rw [hag.layout]
  rw [← hkey]
  have hl : Spec.Dsa.lengthsValid c.key.pLen c.key.qLen := c.input.lengths
  unfold Spec.Dsa.lengthsValid at hl
  have hscr : Scr s c.input.base deriveExtent := c.pre.scratch.congr hk.2.2
  have hn := hscr.nowrap
  obtain ⟨_, _, _, hxs⟩ := c.pre.sources hframe hk
  have hparams := c.pre.paramsSource.congrK hframe hk
  have hf (f : Field) (hf : f ≠ .mask) : word s.mem c.input.base f.offset = c.layout.fields f := hr.fields f hf
  refine ⟨hr.parent.rdi, scratch_prefix (n := pWorkspace) hscr (by decide) (by decide),
    ⟨valid, hf .out (by decide), hf .p (by decide), hf .y (by decide), hf .x (by decide),
      (hf .pLen (by decide)).trans c.pre.pLength, hf .qLen (by decide), hm⟩,
    by omega_using [hl], by omega_using [hl], by omega_using [hl],
    ⟨fun i hi => by rw [hk.2.1, hk.2.2]; exact c.pre.paramsSource.rd i (by rw [c.input.paramsLength]; exact hi),
      c.pre.paramsOut⟩,
    ⟨fun i hi => by
      change InRegions (s.rd ++ s.wr) (off c.input.base derivedY + BitVec.ofNat 64 i) 1
      rw [off_add]
      exact scr_byte_rd hscr (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hl]),
     fun i hi j hj => scr_ne_out c.pre.outSeparate (d := derivedY) (i := i)
      (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hl]) (by omega_using [hn]) j hj⟩,
    ⟨fun i hi => by rw [hk.2.1, hk.2.2]; exact c.pre.xSource.rd i (by rw [c.input.xLength]; exact hi),
      c.pre.xOut⟩,
    fun i hi => by rw [hk.2.2]; exact c.pre.outWrite i hi⟩

theorem deriveComputed_ok (M : Mont) (Sq : MontS) {reference : AcceptedDeriveCall} {s : State}
    (h : DeriveReady reference.val s) :
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
      Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, Checks.signingKey Sq.mm M.mm]) s (DeriveComputed reference.val) := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, hframe, hk⟩ := h
  have hac : c.input.accepted = true := hag.accepted.trans reference.property
  obtain ⟨hsize, hpo, hqo⟩ := c.input.shapeFacts hac
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hpf : Spec.Dsa.decodeBE c.input.pb ≤ 256 ^ c.input.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.pb; rw [c.input.pbLength] at hh; exact Nat.le_of_lt hh
  have hqf : Spec.Dsa.decodeBE c.input.qb ≤ 256 ^ c.input.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.qb; rw [c.input.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.mono (deriveBody_ok (L := c.layout.withInverses pi qi) M Sq hr (c.pre.scratch.congr hk.2.2)
    hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar c.input.gbLength c.input.qbLength
    c.input.xLength rfl rfl hm) fun t ⟨ht, hmt, _, hft, hkt⟩ => ?_
  exact ⟨c, hag, pi, qi, _, ht, hmt, hframe.trans (InScr.of_outside hft (by decide)),
    (hk.trans hkt).mono (by decide)⟩

theorem deriveSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedDeriveCall => DeriveShaped c.val))
      (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
        Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, Checks.signingKey Sq.mm M.mm, Generate.writeKey, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq deriveWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.range qWorkspace Core.privateScalar,
    Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, Checks.signingKey Sq.mm M.mm]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine RelCT.seq (R := Two (fun c : AcceptedDeriveCall => DeriveComputed c.val))
    (two_post ((deriveBodySched_ct M Sq).mono (fun _ _ h => deriveReady_related h) (fun _ _ h => h))
      (fun reference s h => deriveComputed_ok M Sq h)) ?_
  unfold seqs
  exact RelCT.seq (two_map (fun c : AcceptedDeriveCall => c.val.key) (fun _ _ h => h.key) writeKey_ct)
    (two_map (fun k : KeyPublic => k.base) (fun _ _ h => h) result_ct)

theorem deriveMain_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two DeriveStart) (Generate.deriveKey Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq deriveShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map DeriveCall.failure (fun _ _ h => h.failure) deriveFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (deriveSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.DeriveChecked`, which only this module used -/

section

/-! # Functional correctness of x86-64 DSA key derivation for a checked domain

`Generate.deriveChecked` is `Generate.deriveKey` without the exponentiation
`g^q mod p = 1`: for a domain whose check has succeeded, the remaining
checks of the signer accept exactly what the full ones do. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The signer's checks of g and y but `g^q = 1`, as `signingKeyAccepted`. -/
def prefixAccepted (L : ExecutionLayout) (gb yb : List Byte) (valid : Bool) : Bool :=
  decide ((L.modulus - 1) % L.subgroup = 0) &&
  (decide (1 < Spec.Dsa.decodeBE yb ∧ Spec.Dsa.decodeBE yb < L.modulus) &&
  (decide (1 < Spec.Dsa.decodeBE gb ∧ Spec.Dsa.decodeBE gb < L.modulus) && valid))

theorem keyPrefix_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb yb qb : List Byte}
    (hg : OperandBytes s0 L.base usedBytes Core.generator gb)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue yb)
    (hqb : OperandBytes s0 L.base usedBytes ⟨.input .q, .qLen⟩ qb)
    (hgl : gb.length = L.pLen) (hyl : yb.length = L.pLen)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (seqs (Checks.publicPrefix M.mm)) s0 fun s6 =>
      Ready L s6 ∧ word s6.mem L.base Field.mask.offset = mask (prefixAccepted L gb yb valid) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s6.mem ∧ Keep coreRegs s0 s6 := by
  obtain ⟨hql, hqu, hqp, hpu⟩ := L.widths
  have fitq (n : Nat) (h : n < L.subgroup) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.qLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hqf)
  have fitp (n : Nat) (h : n < L.modulus) : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE L.pLen n) = n :=
    decodeBE_encodeBE (Nat.lt_of_lt_of_le h hpf)
  have ht : t + L.pLen ≤ usedBytes := by unfold t usedBytes; omega
  have hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega
  unfold Checks.publicPrefix seqs
  refine WP.seq (WP.mono (readyRange_ok h0 .p Core.generator (by trivial) hg.active
    (by rw [hgl]; omega) (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true hm) fun s1 h1 => ?_)
  have hg1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg
  have hy1 := h1.preserve h0 (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy
  have hq1 := h1.preserve h0 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb
  refine WP.seq (WP.mono (readyRange_ok h1.ready .p Core.publicValue (by trivial) hy1.active
    (by rw [hyl]; omega) (by simp only [hyl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    true h1.mask) fun s2 h2 => ?_)
  have hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  have hq2 := h2.preserve h1.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq1
  refine WP.seq (WP.mono (readyMinus_ok h2.ready .p 1 (by decide) (by change 1 ≤ L.modulus; omega)
    t (by decide) ht) fun s3 h3 => ?_)
  have hg3 := h3.external (by decide) ht hg2
  have hq3 := h3.external (by decide) ht hq2
  have hm3 := (h3.fields (by decide) ht .mask).trans h2.mask
  have step4 := readyReduce_ok M h3.ready hq hoq (Core.element t) (by change t < 2 ^ 31; decide)
    (h3.output (by decide) ht) (by simp only [encodeBE_length, ModulusSide.length]; omega) u (by decide) hu
  have step4' : WP isa (Core.reduce M.mm (Core.element t) (Core.scalar u)) s3
      (CallResult L .q u ((L.modulus - 1) % L.subgroup) s3) := by
    simpa only [ModulusSide.length, ModulusSide.value, fitp (L.modulus - 1) (by omega)] using step4
  refine WP.seq (WP.mono step4' fun s4 h4 => ?_)
  have hg4 := h4.external (by decide) hu hg3
  have hq4 := h4.external (by decide) hu hq3
  have hm4 := (h4.fields (by decide) hu .mask).trans hm3
  refine WP.seq (WP.mono (readyZero_ok h4.ready (Core.scalar u) (by change u < 2 ^ 31; decide)
    (h4.output (by decide) hu) (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) false hm4) fun s5 h5 => ?_)
  have hziff : (∀ b ∈ Spec.Dsa.encodeBE L.qLen ((L.modulus - 1) % L.subgroup), b = 0) ↔
      (L.modulus - 1) % L.subgroup = 0 := by
    rw [← VG.Proof.Dsa.decodeBE_eq_zero, fitq _ (Nat.mod_lt _ (by omega))]
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length] at hm5
  simp only [hziff] at hm5
  have hg5 := h5.preserve h4.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg4
  have hq5 := h5.preserve h4.ready (by decide) (by decide) (by change Field.q ≠ .mask; decide) hq4
  refine WP.mono (readyMinus_ok h5.ready .q 2 (by decide) (by change 2 ≤ L.subgroup; omega)
    qMinusTwo (by decide) hqm) fun s6 h6 => ?_
  refine ⟨h6.ready, (h6.fields (by decide) hqm .mask).trans hm5, ?_, ?_⟩
  · exact ((((h1.scheduleFrame.trans h2.scheduleFrame).trans (h3.scheduleFrame (by decide) ht)).trans
      (h4.scheduleFrame (by decide) hu)).trans h5.scheduleFrame).trans (h6.scheduleFrame (by decide) hqm)
  · exact (((((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep).trans h5.keep).trans h6.keep).mono (by decide)

/-- What domain-checked derivation computes before writing the key: x's
range, y = g^x copied past the signer's layout, and the signer's checks with
that y but `g^q = 1`. -/
theorem deriveCheckedBody_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s : State} (hr : Ready L s)
    (hs : Scr s L.base deriveExtent)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup) (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb qb xb : List Byte}
    (hg : OperandBytes s L.base deriveExtent Core.generator gb)
    (hqb : OperandBytes s L.base deriveExtent ⟨.input .q, .qLen⟩ qb)
    (hx : OperandBytes s L.base deriveExtent Core.privateScalar xb)
    (hgl : gb.length = L.pLen) (hxl : xb.length = L.qLen) (hy : L.fields .y = off L.base derivedY)
    (hm : word s.mem L.base Field.mask.offset = mask true) :
    let y := Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE xb) L.modulus
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
        Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, seqs (Checks.publicPrefix M.mm)]) s fun t =>
      Ready L t ∧
      word t.mem L.base Field.mask.offset = mask (prefixAccepted L gb (Spec.Dsa.encodeBE L.pLen y)
        (decide (0 < Spec.Dsa.decodeBE xb ∧ Spec.Dsa.decodeBE xb < L.subgroup) && true)) ∧
      (∀ i (hi : i < L.pLen), t.mem (off L.base derivedY + BitVec.ofNat 64 i) =
        (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)) ∧
      Outside L.base 128 (deriveExtent - 128) s.mem t.mem ∧ Keep coreRegs s t := by
  intro y
  obtain ⟨hql1, hqu, hqp, hpu⟩ := L.widths
  obtain hp384 : 0 < L.pLen ∧ L.pLen ≤ 384 := by
    obtain hl := L.lengths; unfold Spec.Dsa.lengthsValid at hl; omega_using [hl]
  obtain hend : t2 + L.pLen ≤ usedBytes := by unfold t2 usedBytes; omega_using [hp384]
  unfold seqs
  -- 0 < x < q
  refine WP.seq (WP.mono (readyRange_ok hr .q Core.privateScalar (by trivial) (hx.shrink (by decide)).active
    (by rw [hxl]; omega_using [hql1]) (by simp only [hxl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm) fun s1 h1 => ?_)
  obtain hf1 : Outside L.base 128 (deriveExtent - 128) s.mem s1.mem := h1.frame.mono (by decide) (by decide)
  obtain hg1 := hg.frame hr h1.ready hf1 h1.keep (by decide) (by simp [stablePointer, Core.generator])
  obtain hq1 := hqb.frame hr h1.ready hf1 h1.keep (by decide) (by change Field.q ≠ .mask; decide)
  obtain hx1 := hx.frame hr h1.ready hf1 h1.keep (by decide) (by simp [stablePointer, Core.privateScalar])
  -- y = g^x mod p, at t2
  obtain step2 := readyPow_ok M Sq h1.ready .p hp hpo Core.generator Core.privateScalar (by trivial) (by trivial)
    (hg1.shrink (by decide)).active (hx1.shrink (by decide)).active (by rw [hgl]; omega_using [hp384])
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hxl]; omega_using [hql1]) (by rw [hxl]; omega_using [hqu]) t2 (by decide) hend
  obtain step2' : WP isa (Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2)) s1
      (CallResult L .p t2 y s1) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value] using step2
  refine WP.seq (WP.mono step2' fun s2 h2 => ?_)
  obtain hf2 : Outside L.base 128 (deriveExtent - 128) s1.mem s2.mem :=
    (h2.scheduleFrame (by decide) hend).mono (by decide) (by decide)
  obtain hg2 := hg1.frame h1.ready h2.ready hf2 h2.keep (by decide) (by simp [stablePointer, Core.generator])
  obtain hq2 := hq1.frame h1.ready h2.ready hf2 h2.keep (by decide) (by change Field.q ≠ .mask; decide)
  obtain hm2 := (h2.fields (by decide) hend .mask).trans h1.mask
  obtain hs2 : Scr s2 L.base deriveExtent := hs.congr (h1.keep.trans h2.keep).2.2
  -- y, copied past the signer's layout
  refine WP.seq (WP.mono (copyY_ok h2.ready hs2) fun s3 ⟨h3, hy3, hf3o, hk3⟩ => ?_)
  obtain hf3 : Outside L.base 128 (deriveExtent - 128) s2.mem s3.mem :=
    hf3o.mono (by decide) (by unfold deriveExtent; omega_using [hp384])
  obtain hg3 := hg2.frame h2.ready h3 hf3 hk3 (by decide) (by simp [stablePointer, Core.generator])
  obtain hq3 := hq2.frame h2.ready h3 hf3 hk3 (by decide) (by change Field.q ≠ .mask; decide)
  obtain hm3 : word s3.mem L.base Field.mask.offset = mask (decide (0 < Spec.Dsa.decodeBE xb ∧
      Spec.Dsa.decodeBE xb < L.subgroup) && true) := by
    refine (hf3o.word (Or.inl (by decide)) (by decide)).trans ?_
    simpa only [Bool.false_eq_true, ↓reduceIte, ModulusSide.value] using hm2
  obtain hyb : ∀ i (hi : i < L.pLen), s3.mem (off L.base derivedY + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi) := by
    intro i hi
    rw [hy3 i hi]
    obtain hb := congrArg (fun l => l[i]?) h2.bytes
    simp only [ModulusSide.length, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi,
      Option.map_some] at hb
    rw [List.getElem?_eq_getElem (by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)] at hb
    exact Option.some.inj hb
  obtain hys : OperandBytes s3 L.base usedBytes Core.publicValue (Spec.Dsa.encodeBE L.pLen y) := by
    refine ⟨(h3.fields .pLen (by decide)).trans (by rw [VG.Proof.Dsa.encodeBE_length]; exact L.pLength), ?_⟩
    simp only [Core.publicValue, pointerValue, h3.fields .y (by decide), hy]
    refine ⟨fun i hi => ?_, fun i hi => hyb i (by rwa [VG.Proof.Dsa.encodeBE_length] at hi), fun i hi => ?_⟩
    · rw [VG.Proof.Dsa.encodeBE_length] at hi
      rw [off_add]
      exact scr_byte_rd (hs.congr (h1.keep.trans (h2.keep.trans hk3)).2.2)
        (by unfold deriveExtent; omega_using [hi, hp384])
    · rw [VG.Proof.Dsa.encodeBE_length] at hi
      rw [ofs_off _ (by have := hs.nowrap; unfold deriveExtent at this; omega_using [this, hi, hp384])]
      exact Nat.le_add_right _ _
  -- the signer's checks of the domain and y
  refine WP.mono (keyPrefix_ok M h3 hp hq hpo hqo hpf hqf (hg3.shrink (by decide)) hys (hq3.shrink (by decide))
    hgl (VG.Proof.Dsa.encodeBE_length _ _) hm3) fun t ⟨ht, hmt, hft, hkt⟩ => ?_
  refine ⟨ht, hmt, fun i hi => (hft _ (Or.inr ?_)).trans (hyb i hi), ?_,
    (((h1.keep.trans h2.keep).trans hk3).trans hkt).mono (by decide)⟩
  · rw [ofs_off _ (by have := hs.nowrap; unfold deriveExtent at this; omega_using [this, hi, hp384])]
    exact Nat.le_trans (by decide) (Nat.le_add_right _ _)
  · exact ((hf1.trans hf2).trans hf3).trans (hft.mono (by decide) (by decide))

theorem deriveCheckedSuccess_ok (M : Mont) (Sq : MontS) {p : DeriveInput} {original st : State}
    (h : DerivePre p original) (hs : DeriveShapePost p original h.pLength st) (ha : p.accepted = true)
    (hc : Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
      Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm), Generate.writeKey, .block SignVerify.result]) st
      (DerivePost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  obtain hpf : Spec.Dsa.decodeBE p.pb ≤ 256 ^ p.pLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.pb; rw [p.pbLength] at hh; exact Nat.le_of_lt hh
  obtain hqf : Spec.Dsa.decodeBE p.qb ≤ 256 ^ p.qLen := by
    obtain hh := VG.Proof.Dsa.decodeBE_lt p.qb; rw [p.qbLength] at hh; exact Nat.le_of_lt hh
  have hl := p.lengths
  unfold Spec.Dsa.lengthsValid at hl
  refine WP.seq (WP.mono (deriveInitialize_ok h hs ha) fun u ⟨pi, qi, hr, ho, hm, hsv, hframe, hkeep⟩ => ?_)
  let L := (p.layout original h.pLength).withInverses pi qi
  obtain hsu : Scr u p.base deriveExtent := h.scratch.congr hkeep.2.2
  apply wpAppendSequences (a := [Checks.range qWorkspace Core.privateScalar,
    Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine WP.mono (deriveCheckedBody_ok (L := L) M Sq hr hsu hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar
    p.gbLength p.xLength rfl hm) fun v ⟨hv, hmv, hyv, hfv, hkv⟩ => ?_
  obtain hframe' : InScr p.base deriveExtent original.mem v.mem :=
    hframe.trans (InScr.of_outside hfv (by decide))
  obtain hkeep' : Keep coreRegs original v := (hkeep.trans hkv).mono (by decide)
  obtain hsv' : Scr v p.base deriveExtent := h.scratch.congr hkeep'.2.2
  obtain ⟨_, _, _, hxs⟩ := h.sources hframe' hkeep'
  obtain hparams := h.paramsSource.congrK hframe' hkeep'
  set valid := prefixAccepted L p.gb p.yb
    (decide (0 < Spec.Dsa.decodeBE p.x ∧ Spec.Dsa.decodeBE p.x < L.subgroup) && true) with hvalid
  obtain hfields : KeyFields v p.base (original.gpr .rdi) (original.gpr .rdx) (off p.base derivedY)
      (original.gpr .r9) p.pLen p.qLen valid :=
    ⟨hv.fields .out (by decide), hv.fields .p (by decide), hv.fields .y (by decide),
      hv.fields .x (by decide), (hv.fields .pLen (by decide)).trans h.pLength,
      hv.fields .qLen (by decide), hmv⟩
  have hn := hsv'.nowrap
  obtain hp384 : p.pLen ≤ 384 := by omega_using [hl]
  obtain hpq : 0 < p.pLen ∧ 0 < p.qLen := by omega_using [hl]
  have hreg : v.rd = original.rd ∧ v.wr = original.wr := hkeep'.2
  unfold seqs
  refine WP.seq (WP.mono (writeKey_ok hsv' hv.parent.rdi (by decide) hfields hpq.1 hpq.2 (by omega_using [hl])
    ⟨fun i hi => hparams.rd i (by rw [p.paramsLength]; exact hi), h.paramsOut⟩
    ⟨fun i hi => by
      rw [off_add]; exact scr_byte_rd hsv' (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hp384]),
     fun i hi j hj => scr_ne_out h.outSeparate (d := derivedY) (i := i)
      (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hp384]) (by omega_using [hn]) j hj⟩
    ⟨fun i hi => hxs.rd i (by rw [p.xLength]; exact hi), h.xOut⟩
    (fun i hi => by rw [hreg.2]; exact h.outWrite i hi))
    fun w ⟨hw₁, hw₂, hw₃, hwf, hkw⟩ => ?_)
  obtain hwv : ∀ d, d + 8 ≤ deriveExtent → word w.mem p.base d = word v.mem p.base d := fun d hd =>
    Mem.readW_congr fun b hb => hwf _ (scr_ne_out h.outSeparate (d := d) (i := b) (by omega_using [hd, hb]) (by omega_using [hn]))
  refine WP.mono (result_ok (hsv'.congr hkw.2.2) ((hkw.gpr (by decide)).trans hv.parent.rdi) (by decide)
    ((hwv _ (by decide)).trans hmv)) fun t ⟨hret, hsave, hmem, hkt⟩ => ?_
  obtain hyfit : p.y < 256 ^ p.pLen :=
    Nat.lt_of_lt_of_le (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp1])) hpf
  obtain hres : Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x =
      if valid then some (p.params ++ p.yb ++ p.x) else none := by
    obtain hg : Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.qb) (Spec.Dsa.decodeBE p.pb) = 1 := by
      rw [p.check_eq, ha, Bool.true_and] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1
    rw [p.derive_eq, ha, Bool.true_and, hvalid, decide_eq_true hg, Bool.true_and]
    unfold prefixAccepted
    rw [VG.Proof.Dsa.decodeBE_encodeBE hyfit]
    rfl
  obtain hlen : p.outLen = p.params.length + p.yb.length + p.x.length := by
    rw [p.paramsLength, VG.Proof.Dsa.encodeBE_length, p.xLength]; unfold DeriveInput.outLen; omega_arith
  refine ⟨?_, ?_, fun i hi => (hsave i hi).trans ((hwv _ (by unfold deriveExtent derivedY usedBytes; omega_using [hi])).trans
      ((hfv.word (Or.inl (by omega_using [hi])) (by omega_using [hi])).trans (hsv i hi))), ?_,
    ((hkeep'.trans hkw).trans hkt).mono (by decide)⟩
  · rw [hret]
    change BitVec.ofNat 64 valid.toNat = _
    rw [hres]
    cases valid <;> rfl
  · rw [hmem, hres]
    cases hvb : valid
    · apply bytesAt_zero_list
      intro i hi
      by_cases h1 : i < 2 * p.pLen + p.qLen
      · rw [hw₁ i h1, hvb]; rfl
      by_cases h2 : i < 3 * p.pLen + p.qLen
      · have := hw₂ (i - (2 * p.pLen + p.qLen)) (by omega_arith)
        rw [show 2 * p.pLen + p.qLen + (i - (2 * p.pLen + p.qLen)) = i by omega_arith, hvb] at this
        exact this
      · have := hw₃ (i - (3 * p.pLen + p.qLen)) (by unfold DeriveInput.outLen at hi; omega_arith)
        rw [show 3 * p.pLen + p.qLen + (i - (3 * p.pLen + p.qLen)) = i by omega_arith, hvb] at this
        exact this
    · simp only [↓reduceIte, Option.getD_some]
      rw [hlen]
      apply bytesAt_key
      · intro i hi
        rw [p.paramsLength] at hi
        rw [hw₁ i hi, hvb]
        simp only [↓reduceIte]
        exact hparams.val i (by rw [p.paramsLength]; exact hi)
      · intro i hi
        rw [VG.Proof.Dsa.encodeBE_length] at hi
        rw [p.paramsLength, hw₂ i hi, hvb]
        simp only [↓reduceIte]
        exact hyv i hi
      · intro i hi
        rw [p.xLength] at hi
        rw [p.paramsLength, VG.Proof.Dsa.encodeBE_length,
          show 2 * p.pLen + p.qLen + p.pLen = 3 * p.pLen + p.qLen by omega_arith, hw₃ i hi, hvb]
        simp only [↓reduceIte]
        exact hxs.val i (by rw [p.xLength]; exact hi)
  · intro x hx hout
    rw [hmem, hwf x hout]
    exact hframe' x hx

theorem deriveCheckedMain_ok (M : Mont) (Sq : MontS) {p : DeriveInput} {s0 : State} (h : DerivePre p s0)
    (hc : Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params = true) :
    WP isa (Generate.deriveChecked Sq.mm M.mm) s0 (DerivePost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (deriveShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => deriveRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => deriveCheckedSuccess_ok M Sq h hs ha hc)
    change eval .e s = some false
    simp only [eval, hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of x86-64 DSA key derivation for a checked domain -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem deriveCheckedBodySched_ct (M : Mont) (Sq : MontS) : RelCT isa (Two DeriveSched)
    (seqs [Checks.range qWorkspace Core.privateScalar,
      Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (fun _ _ => True) := by
  have h4 := publicPrefix_ct M deriveInputs (fun p => deriveInputs_stable p)
    (by intro p; simp [deriveInputs]) (by intro p; simp [deriveInputs])
  unfold seqs
  refine RelCT.seq deriveRange_ct (RelCT.seq (derivePow_ct M Sq) (RelCT.seq deriveCopy_ct ?_))
  exact (two_map (Φ := DeriveSched) (fun p => p) (fun p s h => h.1) h4).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem deriveCheckedComputed_ok (M : Mont) (Sq : MontS) {reference : AcceptedDeriveCall} {s : State}
    (h : DeriveReady reference.val s) :
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
      Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, seqs (Checks.publicPrefix M.mm)]) s (DeriveComputed reference.val) := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, hframe, hk⟩ := h
  have hac : c.input.accepted = true := hag.accepted.trans reference.property
  obtain ⟨hsize, hpo, hqo⟩ := c.input.shapeFacts hac
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hpf : Spec.Dsa.decodeBE c.input.pb ≤ 256 ^ c.input.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.pb; rw [c.input.pbLength] at hh; exact Nat.le_of_lt hh
  have hqf : Spec.Dsa.decodeBE c.input.qb ≤ 256 ^ c.input.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.qb; rw [c.input.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.mono (deriveCheckedBody_ok (L := c.layout.withInverses pi qi) M Sq hr (c.pre.scratch.congr hk.2.2)
    hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar c.input.gbLength
    c.input.xLength rfl hm) fun t ⟨ht, hmt, _, hft, hkt⟩ => ?_
  exact ⟨c, hag, pi, qi, _, ht, hmt, hframe.trans (InScr.of_outside hft (by decide)),
    (hk.trans hkt).mono (by decide)⟩

theorem deriveCheckedSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedDeriveCall => DeriveShaped c.val))
      (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
        Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, seqs (Checks.publicPrefix M.mm), Generate.writeKey, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq deriveWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.range qWorkspace Core.privateScalar,
    Core.pow Sq.mm M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, seqs (Checks.publicPrefix M.mm)]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine RelCT.seq (R := Two (fun c : AcceptedDeriveCall => DeriveComputed c.val))
    (two_post ((deriveCheckedBodySched_ct M Sq).mono (fun _ _ h => deriveReady_related h) (fun _ _ h => h))
      (fun reference s h => deriveCheckedComputed_ok M Sq h)) ?_
  unfold seqs
  exact RelCT.seq (two_map (fun c : AcceptedDeriveCall => c.val.key) (fun _ _ h => h.key) writeKey_ct)
    (two_map (fun k : KeyPublic => k.base) (fun _ _ h => h) result_ct)

theorem deriveCheckedMain_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two DeriveStart) (Generate.deriveChecked Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq deriveShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map DeriveCall.failure (fun _ _ h => h.failure) deriveFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (deriveCheckedSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.KeygenCalls`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.DeriveVerified`, which this module and modules that import it used -/

section

/-! # x86-64 DSA key derivation verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem stackArgs_three (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem disjoint_byte_ne {p q : Addr} {n m i j : Nat} (h : (⟨p, n⟩ : Region).Disjoint ⟨q, m⟩)
    (hi : i < n) (hj : j < m) (hn : n ≤ 2 ^ 64) (hm : m ≤ 2 ^ 64) :
    p + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j := fun he =>
  h _ (contains_byte p hi hn) (he ▸ contains_byte q hj hm)

structure DeriveABI (s : State) : Prop where
  stackBound : (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArgAddr s 0, 24⟩]
  wr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]
  outParams : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  outScalar : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  outScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  paramsScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  scalarScratch : (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  scratchArgs : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 24⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  outBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  paramsBound : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  scalarBound : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .r8).toNat (stackArg s 0).toNat
  outLength : (s.gpr .rsi).toNat = 3 * (s.gpr .r8).toNat + 2 * (stackArg s 0).toNat
  paramsLength : (s.gpr .rcx).toNat = 2 * (s.gpr .r8).toNat + (stackArg s 0).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 2).toNat

theorem deriveABI_of {s : State} (h : (Spec.Dsa.deriveKeyContract abi).pre s) : DeriveABI s := by
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at h
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at h
  sig_split h
  constructor <;> with_reducible assumption

def DeriveABI.input {s : State} (h : DeriveABI s) : DeriveInput where
  base := stackArg s 1
  pLen := (s.gpr .r8).toNat
  qLen := (stackArg s 0).toNat
  params := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
  lengths := h.lengths
  paramsLength := (bytesAt_length _ _ _).trans h.paramsLength
  x := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
  xLength := bytesAt_length _ _ _

theorem DeriveABI.used {s : State} (h : DeriveABI s) : deriveExtent ≤ (stackArg s 2).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 16096 ≤ _
  omega_arith

theorem DeriveABI.pre {s : State} (h : DeriveABI s) : DerivePre h.input s := by
  have hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 24⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  have hout : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have hol : h.input.outLen = (s.gpr .rsi).toNat := h.outLength.symm
  have hu : usedBytes ≤ deriveExtent := by decide
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, (ofNat_toNat64 _).symm, rfl, (ofNat_toNat64 _).symm,
    source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .rcx).isLt) h.paramsScratch) h.used,
    source_shrink (src_of_region (p := s.gpr .r9) (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 0).isLt)
      h.scalarScratch) h.used, ?_, ?_, ?_, ?_⟩
  · intro j hj hb
    exact stackWord_read (count := 3) hargs hj (by omega_arith) (by decide)
  · intro j hj hb i hi
    exact Nat.le_trans (Nat.le_trans hu h.used)
      (stackWord_separate (count := 3) h.scratchArgs hj (by omega_arith) (by decide) i hi)
  · intro i hi
    rw [hol] at hi
    exact ⟨_, hout, contains_byte _ hi (Nat.le_of_lt (s.gpr .rsi).isLt)⟩
  · intro i hi
    rw [hol] at hi
    exact Nat.le_trans h.used (out_scr h.outScratch (contains_byte _ hi (Nat.le_of_lt (s.gpr .rsi).isLt)))
  · intro i hi j hj
    rw [hol] at hj
    exact (disjoint_byte_ne h.outParams hj (by rw [h.paramsLength]; exact hi)
      (Nat.le_of_lt (s.gpr .rsi).isLt) (Nat.le_of_lt (s.gpr .rcx).isLt)).symm
  · intro i hi j hj
    rw [hol] at hj
    exact (disjoint_byte_ne h.outScalar hj hi
      (Nat.le_of_lt (s.gpr .rsi).isLt) (Nat.le_of_lt (stackArg s 0).isLt)).symm

def DeriveABI.call {s : State} (h : DeriveABI s) : DeriveCall := ⟨h.input, s, h.pre⟩

theorem deriveGprPreserved {s t : State} (h : DeriveABI s) (hp : DerivePost h.input s t) :
    gprPreserved s t := by
  obtain ⟨_, _, hsaved, hf, hk⟩ := hp
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
  · refine hf _ (Nat.le_trans h.used (out_scr h.retScratch
      (contains_byte (s.gpr .rsp) (i := i) (len := 8) hi (by decide)))) fun j hj => ?_
    have hol : h.input.outLen = (s.gpr .rsi).toNat := h.outLength.symm
    rw [hol] at hj
    exact disjoint_byte_ne h.retOut hi hj (by decide) (Nat.le_of_lt (s.gpr .rsi).isLt)

theorem deriveSharedPost {s t : State} (h : DeriveABI s) (hp : DerivePost h.input s t) :
    (Spec.Dsa.deriveKeyContract abi).post s t := by
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three]
  have hol : h.input.outLen = (s.gpr .rsi).toNat := h.outLength.symm
  obtain ⟨hret, hbytes, _⟩ := hp
  refine ⟨?_, ?_⟩
  · rw [hret]
    change _ = Spec.Dsa.signStatus (Spec.Dsa.deriveKeyBytes h.input.pLen h.input.qLen h.input.params h.input.x)
    cases Spec.Dsa.deriveKeyBytes h.input.pLen h.input.qLen h.input.params h.input.x <;> rfl
  · rw [← hol]
    exact hbytes

theorem deriveCorrect (M : Mont) (Sq : MontS)
    (hmx : (Generate.deriveKey Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.deriveKeyContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.deriveKey Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.deriveKeyContract abi).post s t := by
  have ha := deriveABI_of h
  obtain ⟨trace, t, he, hp⟩ := deriveMain_ok M Sq ha.pre
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (deriveGprPreserved ha hp), deriveSharedPost ha hp⟩

theorem ExecutionLayout.ext' {L₁ L₂ : ExecutionLayout} (hb : L₁.base = L₂.base) (hp : L₁.pLen = L₂.pLen)
    (hq : L₁.qLen = L₂.qLen) (hm : L₁.modulus = L₂.modulus) (hs : L₁.subgroup = L₂.subgroup)
    (hpi : L₁.pInverse = L₂.pInverse) (hqi : L₁.qInverse = L₂.qInverse) (hf : L₁.fields = L₂.fields) :
    L₁ = L₂ := by
  cases L₁
  cases L₂
  simp only at hb hp hq hm hs hpi hqi hf
  subst hb hp hq hm hs hpi hqi hf
  rfl

theorem derivePublicRelated {s₁ s₂ : State} (h₁ : DeriveABI s₁) (h₂ : DeriveABI s₂)
    (h : (Spec.Dsa.deriveKeyContract abi).pub s₁ s₂) : Two DeriveStart s₁ s₂ := by
  sig_pub [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, _, h8, h9, a0, a1, _⟩ := h
  have hpub := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpub
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat h8
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat a0
  have hpb : h₁.input.params = h₂.input.params := hb
  have hpb' : h₁.input.pb = h₂.input.pb := by
    change h₁.input.params.take h₁.input.pLen = h₂.input.params.take h₂.input.pLen
    rw [hpb, hp]
  have hqb' : h₁.input.qb = h₂.input.qb := by
    change (h₁.input.params.drop h₁.input.pLen).take h₁.input.qLen =
      (h₂.input.params.drop h₂.input.pLen).take h₂.input.qLen
    rw [hpb, hp, hq]
  have hac : h₁.input.accepted = h₂.input.accepted := by
    unfold ParametersInput.accepted
    congr 1
  have hlayout : h₁.call.layout = h₂.call.layout := by
    have hf : deriveFieldValues s₁ (BitVec.ofNat 64 h₁.input.qLen) h₁.input.base h₁.input.accepted =
        deriveFieldValues s₂ (BitVec.ofNat 64 h₂.input.qLen) h₂.input.base h₂.input.accepted := by
      have hbase : h₁.input.base = h₂.input.base := a1
      funext f
      cases f <;> simp only [deriveFieldValues, hdi, hdx, h8, h9, hq, hbase, hac]
    exact ExecutionLayout.ext' a1 hp hq (congrArg Spec.Dsa.decodeBE hpb') (congrArg Spec.Dsa.decodeBE hqb')
      (show (0 : BitVec 64) = 0 from rfl) (show (0 : BitVec 64) = 0 from rfl) hf
  exact ⟨h₂.call, ⟨h₁.call, ⟨hlayout, hpb, hsp⟩, rfl⟩, ⟨h₂.call, ⟨rfl, rfl, rfl⟩, rfl⟩⟩

theorem deriveConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (Spec.Dsa.deriveKeyContract abi).pre
      (Spec.Dsa.deriveKeyContract abi).pub (Generate.deriveKey Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (deriveMain_ct M Sq _ _ _ _ _ _
    (derivePublicRelated (deriveABI_of h₁) (deriveABI_of h₂) hp) e₁ e₂).1

/-- An ordinary 1024/160 call with disjoint buffers. The all-zero domain is
allowed by the contract and rejected by the program. -/
def deriveSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 424 | .rdx => 0x2000 | .rcx => 276
    | .r8 => 128 | .r9 => 0x3000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10008 then 20 else if a = 0x10011 then 0x80 else if a = 0x10019 then 8 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x3000, 20⟩, ⟨0x10008, 24⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x8000, 16384⟩]

end VG.Proof.Dsa.X86_64

end

end

/-! # The domain check and key derivation with call-based arithmetic backends -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem parameters_implies8 :
    (Proof.Dsa.checkParametersContract abi).Implies (Proof.Dsa.checkParametersContract abi 8) where
  pre := by
    intro s h
    sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop] at h
    sig_split h
    sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs,
    stackArgs_zero, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop]
      [parametersSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using parametersSatState

theorem derive_implies8 : (Spec.Dsa.deriveKeyContract abi).Implies (Spec.Dsa.deriveKeyContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop] at h
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
    sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop]
      [deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using deriveSatState

theorem parameters_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hp : (Proof.Dsa.checkParametersContract abi).post s b) :
    (Proof.Dsa.checkParametersContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero, List.range, List.range.loop] at hp ⊢
  simpa only [State.patch_gpr] using hp

theorem derive_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Dsa.deriveKeyContract abi).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (Spec.Dsa.deriveKeyContract abi).post s b) :
    (Spec.Dsa.deriveKeyContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have ha := deriveABI_of hs
  have hm := Clear.miss_wr hc (by rw [ha.wr]; exact List.mem_cons_self) ha.outBound (Nat.le_refl _)
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range, List.range.loop] at hp ⊢
  simpa only [State.patch_gpr, patch_mem, bytesAt_overlay hm] using hp

theorem parameters_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = Generate.checkParameters Sq.mm M.mm)
    (hmx : (Generate.checkParameters Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Proof.Dsa.checkParametersContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ parametersCorrect M Sq hmx) (hin ▸ parametersConstantTime M Sq)
    parameters_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    (fun s b hv u _ _ hp => parameters_patch s b hv u hp)

theorem derive_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = Generate.deriveKey Sq.mm M.mm)
    (hmx : (Generate.deriveKey Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.deriveKeyContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ deriveCorrect M Sq hmx) (hin ▸ deriveConstantTime M Sq)
    derive_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    derive_patch

end VG.Proof.Dsa.X86_64

end

end

/-! # x86-64 DSA key derivation for a checked domain, against its contract

`Generate.deriveChecked` is verified against `deriveKeyDomainCheckedContract`
(`Spec/Dsa/DomainChecked.lean`): `deriveKeyContract` under the precondition
that the exact domain bytes pass `checkParametersBytes`. Key generation calls
it once its domain check has returned 1. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64

theorem deriveChecked_pre {s : State} {stack : Nat}
    (h : (Spec.Dsa.deriveKeyDomainCheckedContract abi stack).pre s) :
    (Spec.Dsa.deriveKeyContract abi stack).pre s ∧
      Spec.Dsa.checkParametersBytes (s.gpr .r8).toNat (stackArg s 0).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) = true := by
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop] at h
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop]
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop]
  sig_and_intros <;> with_reducible assumption

theorem deriveChecked_of_pre {s : State} {stack : Nat} (h : (Spec.Dsa.deriveKeyContract abi stack).pre s)
    (hc : Spec.Dsa.checkParametersBytes (s.gpr .r8).toNat (stackArg s 0).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) = true) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi stack).pre s := by
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop] at h
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three, List.range,
    List.range.loop] at h
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop]
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
    List.range, List.range.loop]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem deriveCheckedCorrect (M : Mont) (Sq : MontS)
    (hmx : (Generate.deriveChecked Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s) :
    ∃ trace t, Exec isa (Generate.deriveChecked Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.deriveKeyDomainCheckedContract abi).post s t := by
  obtain ⟨hd, hc⟩ := deriveChecked_pre h
  have ha := deriveABI_of hd
  obtain ⟨trace, t, he, hp⟩ := deriveCheckedMain_ok M Sq ha.pre hc
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (deriveGprPreserved ha hp), deriveSharedPost ha hp⟩

theorem deriveCheckedConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre
      (Spec.Dsa.deriveKeyDomainCheckedContract abi).pub (Generate.deriveChecked Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (deriveCheckedMain_ct M Sq _ _ _ _ _ _
    (derivePublicRelated (deriveABI_of (deriveChecked_pre h₁).1) (deriveABI_of (deriveChecked_pre h₂).1) hp)
      e₁ e₂).1

/-- `validKeyWitness`'s domain, the first 276 of its bytes. -/
def validDomainWitness : List Byte := VG.Proof.Dsa.validKeyWitness.take 276

theorem validDomainWitness_length : validDomainWitness.length = 276 := by
  simp only [validDomainWitness, List.length_take, VG.Proof.Dsa.validKeyWitness_length]; rfl

theorem validDomainWitness_valid : Spec.Dsa.checkParametersBytes 128 20 validDomainWitness = true := by
  decide +kernel

/-- `deriveSatState` with `validDomainWitness` at `0x2000`. -/
def deriveCheckedSatState : State where
  gpr := deriveSatState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2114 then
    validDomainWitness[a.toNat - 0x2000]?.getD 0 else deriveSatState.mem a
  rd := deriveSatState.rd
  wr := deriveSatState.wr

theorem deriveCheckedSat_domain :
    Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x2000 276 = validDomainWitness :=
  bytesAt_window (base := 0x2000) validDomainWitness_length (by decide) fun a h₁ h₂ => by
    simp only [deriveCheckedSatState]
    exact ite_eq_left ⟨h₁, h₂⟩

theorem deriveCheckedSat_valid : Spec.Dsa.checkParametersBytes 128 20
    (Spec.Rsa.bytesAt deriveCheckedSatState.mem 0x2000 276) = true := by
  rw [deriveCheckedSat_domain]; exact validDomainWitness_valid

theorem deriveCheckedSatisfiable : ∃ s, (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s := by
  have ho : ∃ s, (Spec.Dsa.deriveKeyContract abi).pre s ∧ s = deriveCheckedSatState := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three]
      [deriveCheckedSatState, deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using deriveCheckedSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, deriveChecked_of_pre h deriveCheckedSat_valid⟩

theorem deriveCheckedSatisfiable8 : ∃ s, (Spec.Dsa.deriveKeyDomainCheckedContract abi 8).pre s := by
  have ho : ∃ s, (Spec.Dsa.deriveKeyContract abi 8).pre s ∧ s = deriveCheckedSatState := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop]
      [deriveCheckedSatState, deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using deriveCheckedSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, deriveChecked_of_pre h deriveCheckedSat_valid⟩

theorem derive_checked_verified (M : Mont) (Sq : MontS)
    (hmx : (Generate.deriveChecked Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Generate.deriveChecked Sq.mm M.mm) (Spec.Dsa.deriveKeyDomainCheckedContract abi) :=
  ⟨deriveCheckedCorrect M Sq hmx, deriveCheckedConstantTime M Sq, deriveCheckedSatisfiable⟩

theorem deriveChecked_implies8 :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi).Implies (Spec.Dsa.deriveKeyDomainCheckedContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop] at h
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop]
    sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, stackArgs_three,
      List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs,
    stackArgs_three, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := deriveCheckedSatisfiable8

theorem deriveChecked_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Dsa.deriveKeyDomainCheckedContract abi).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (Spec.Dsa.deriveKeyDomainCheckedContract abi).post s b) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) :=
  derive_patch s b hv u (deriveChecked_pre hs).1 hc hp

theorem derive_checked_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = Generate.deriveChecked Sq.mm M.mm)
    (hmx : (Generate.deriveChecked Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.deriveKeyDomainCheckedContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ deriveCheckedCorrect M Sq hmx) (hin ▸ deriveCheckedConstantTime M Sq)
    deriveChecked_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    deriveChecked_patch

end VG.Proof.Dsa.X86_64
