module

public import VerifiedGarbage.Proof.Dsa.X86_64.Derive
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.X86_64.Derive
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.Layout

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

theorem DeriveAgrees.gb {reference c : DeriveCall} (h : DeriveAgrees reference c) :
    c.input.gb = reference.input.gb := by
  rw [ParametersInput.gb, ParametersInput.gb, h.params, h.pLen, h.qLen]

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
  pBound := by rw [c.input.pbLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega
  qBound := by rw [c.input.qbLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega
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
    omega
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
