module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerInput
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowHalfCT
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowExp

import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnterCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopyCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopy
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPower
import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnter
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerInput
import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrimeCT
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWideCT
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperand
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT
/-! # A factor's narrow private power hides the factor, exponent, input and acceptance

Each stage's paired precondition holds in both runs after the previous stage;
the stages' public data are the workspaces, the widths and the saved lengths.
-/

/-! ## Preparing the factor in the narrow workspace hides the factor and acceptance -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_narrowPrime_ct {base pp : BitVec 32} {len v k ps : Nat} {pb1 pb2 : List Byte}
    (countFits : 128 * v < 2 ^ 32) :
    RelCT isa (fun s t => NarrowPrimeInput base pp len v k ps pb1 s ∧ NarrowPrimeInput base pp len v k ps pb2 t ∧
      s.sp = t.sp) (narrowPrime ps) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => NarrowPrimeInput base pp len v k ps pb1 s ∧
      NarrowPrimeInput base pp len v k ps pb2 t ∧ s.sp = t.sp) (savedOperand 0 ps (ps + 4)) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 0 < 8)).mono
      (fun _ _ h => ⟨⟨h.1.toLayoutFrameReady, h.1.source⟩, ⟨h.2.1.toLayoutFrameReady, h.2.1.source⟩, h.2.2⟩)
      (fun _ _ _ => trivial)
  have wp (s : State) {pb : List Byte} (h : NarrowPrimeInput base pp len v k ps pb s) :
      WP isa (savedOperand 0 ps (ps + 4)) s (AcceptedPrimeInput base len v) :=
    (crt_narrowImport_ok s h).mono fun _ j => j.1
  rw [narrowPrime]
  exact crt_seq_ct load (fun s h => wp s h) (fun s h => wp s h) (prepareAcceptedPrime_ct countFits)

end VG.Proof.Bignum.Arm

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtNarrowExpCT.lean`, which only this module imported.
section

/-! # The narrow exponentiation hides the factor, the reduced input and the exponent -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (arrAt)

theorem crt_narrowExp_ct {base ep : BitVec 32} {len v M1 M2 x1 x2 eLen es : Nat} {eb1 eb2 : List Byte}
    (fit : arrAt v 3 + 32 ≤ 8 * len) (fits : arrAt v 16 ≤ 8 * len) (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => NarrowExpInput base ep len v M1 x1 eLen es eb1 s ∧
      NarrowExpInput base ep len v M2 x2 eLen es eb2 t ∧ s.sp = t.sp) ((narrowExpWith kernel.code) es) (fun _ _ => True) := by
  let Loaded := fun (M x : Nat) (eb : List Byte) (s : State) =>
    NarrowExpInput base ep len v M x eLen es eb s ∧ s.gpr .r1 = ep ∧ s.gpr .r2 = BitVec.ofNat 32 eLen
  have args : RelCT isa (fun s t => NarrowExpInput base ep len v M1 x1 eLen es eb1 s ∧
      NarrowExpInput base ep len v M2 x2 eLen es eb2 t ∧ s.sp = t.sp) (.block (exponentArgs es)) (fun _ _ => True) :=
    (stackLoads_ct [(.r1, es), (.r2, es + 4)]).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have argsWP (s : State) {M x : Nat} {eb : List Byte} (h : NarrowExpInput base ep len v M x eLen es eb s) :
      WP isa (.block (exponentArgs es)) s (Loaded M x eb) :=
    (crt_exponentArgs_ok s h).mono fun _ j => ⟨h.of_mem j.2.2.1 j.2.2.2, j.1, j.2.1⟩
  have controls : RelCT isa (fun s t => Loaded M1 x1 eb1 s ∧ Loaded M2 x2 eb2 t ∧ s.sp = t.sp)
      (.block expControls) (fun _ _ => True) :=
    expControls_ct.mono (fun _ _ h => h.1.1.ready.ptr.trans h.2.1.1.ready.ptr.symm) (fun _ _ _ => trivial)
  let Phase := fun (M x : Nat) (eb : List Byte) (s : State) => ExpPhaseInput base ep len v M x eb s ∧ eb.length = eLen
  have controlsWP (s : State) {M x : Nat} {eb : List Byte} (h : Loaded M x eb s) :
      WP isa (.block expControls) s (Phase M x eb) :=
    (crt_narrowControls_ready s h.1 h.2.1 h.2.2).mono fun _ j => ⟨j.1, h.1.exponent.length⟩
  have phase : RelCT isa (fun s t => Phase M1 x1 eb1 s ∧ Phase M2 x2 eb2 t ∧ s.sp = t.sp)
      kernel.code (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    exact kernel.ct fit fits h.1.1.positive (h.1.2.trans h.2.1.2.symm) s t tr1 tr2 u w
      ⟨h.1.1, h.2.1.1, h.2.2⟩ e1 e2
  rw [narrowExpWith]
  exact crt_seq_ct args (fun s h => argsWP s h) (fun s h => argsWP s h)
    (crt_seq_ct controls (fun s h => controlsWP s h) (fun s h => controlsWP s h) phase)

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

/-- The safe factor that the acceptance bit saved in `s` selects. -/
def narrowM (s : State) (pb : List Byte) : Nat :=
  safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (Spec.Rsa.os2ip pb)

section
variable (g : CrtGeometry) (bs : Fin 7 → List Byte) (child : BitVec 32) (j : Fin 6)

/-- The input imported at the modulus width, and the acceptance bit for the factor. -/
def NarrowAccepted (s : State) : Prop :=
  CrtShared g bs s ∧ (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1 ∧
    ((s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≠ 0 →
      1 < Spec.Rsa.os2ip (bs j.succ) ∧ Spec.Rsa.os2ip (bs j.succ) % 2 = 1)

/-- The narrow workspace selected and set up. -/
def NarrowEntered (s : State) : Prop :=
  NarrowAccepted g bs j s ∧
    LayoutFrameReady (crtN g.base g.words) (workspaceWords g.words) (narrowWords (g.sourceLength j.succ) g.words) s

/-- The factor prepared in the narrow workspace. -/
def NarrowPrepared (s : State) : Prop :=
  CrtShared g bs s ∧
    ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) (narrowWords (g.sourceLength j.succ) g.words) s ∧
    numAt s.mem (State.addr (crtN g.base g.words)) (narrowWords (g.sourceLength j.succ) g.words) 0 =
      narrowM s (bs j.succ) ∧
    narrowM s (bs j.succ) % 2 = 1 ∧
    numAt s.mem (State.addr (crtN g.base g.words)) (narrowWords (g.sourceLength j.succ) g.words) 4 =
      2 ^ (128 * narrowWords (g.sourceLength j.succ) g.words) % narrowM s (bs j.succ)

/-- The reduced input in the narrow workspace, ready for the exponent `i`. -/
def NarrowCopied (i : Fin 6) (s : State) : Prop :=
  CrtShared g bs s ∧ ∃ M x, NarrowExpInput (crtN g.base g.words) (g.source i.succ) (workspaceWords g.words)
    (narrowWords (g.sourceLength j.succ) g.words) M x (g.sourceLength i.succ) (56 + 8 * i.val) (bs i.succ) s

end

theorem NarrowEntered.primeInput {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    {j : Fin 6} (h : NarrowEntered g bs j s) (prime : j = 1 ∨ j = 2) :
    NarrowPrimeInput (crtN g.base g.words) (g.source j.succ) (workspaceWords g.words)
      (narrowWords (g.sourceLength j.succ) g.words) (g.sourceLength j.succ) (56 + 8 * j.val) (bs j.succ) s := by
  obtain ⟨⟨shared, bit, valid⟩, selected⟩ := h
  obtain ⟨_, _, kfit, kpos, _, _, _⟩ := shared.narrow_fits j prime
  have hj := j.isLt
  exact ⟨selected,
    by simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega] using shared.savedOperand j shared.narrow_member,
    kpos, kfit, by have := shared.stack.nowrap; omega, shared.stack.read (by decide), bit, valid⟩

theorem crt_narrowAccepted_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot : Nat} {j i : Fin 6} (h : CrtShared g bs s) (kind : CrtChild g child slot)
    (input : CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words g.length
      (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) s)
    (prime : numAt s.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs j.succ)) :
    WP isa factorInput s (NarrowAccepted g bs j) := by
  refine WP.mono (crt_factorInput_ok s h kind i input) ?_
  rintro u ⟨shared, _, flag, _, _⟩
  exact ⟨shared, by rw [flag]; exact input.accepted.bit, by rw [flag, ← prime]; exact input.accepted.valid⟩

theorem crt_narrowEntered_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    {j : Fin 6} (h : NarrowAccepted g bs j s) (prime : j = 1 ∨ j = 2) :
    WP isa (enterNarrow (56 + 8 * j.val + 4)) s (NarrowEntered g bs j) := by
  obtain ⟨shared, bit, valid⟩ := h
  refine WP.mono (crt_enterNarrow_ok s shared j prime) ?_
  rintro t ⟨sharedT, selected, flag, _, _⟩
  exact ⟨⟨sharedT, by rw [flag]; exact bit, by rw [flag]; exact valid⟩, selected⟩

theorem crt_narrowPrepared_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    {j : Fin 6} (h : NarrowEntered g bs j s) (prime : j = 1 ∨ j = 2) :
    WP isa (narrowPrime (56 + 8 * j.val)) s (NarrowPrepared g bs j) := by
  have shared := h.1.1
  obtain ⟨_, le, _, _, _, _, _⟩ := shared.narrow_fits j prime
  have words : g.words ≤ 128 := (crt_width_valid shared.buffers.lengthValid).2.1
  refine WP.mono (crt_narrowPrime_ok s (h.primeInput prime) (by omega)) ?_
  rintro t ⟨ready, modulus, odd, r2, flag, frame, rest⟩
  have m : narrowM t (bs j.succ) = narrowM s (bs j.succ) := by unfold narrowM; rw [flag]
  unfold NarrowPrepared
  rw [m]
  exact ⟨shared.after_narrow (frame.mono (by simp)) rest, ready, modulus, odd, r2⟩

/-- After the safe factor is copied back: ready to reduce the input. -/
theorem crt_narrowCopiedBack_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot : Nat} {j : Fin 6} (h : NarrowPrepared g bs j s) (kind : CrtChild g child slot) (prime : j = 1 ∨ j = 2) :
    WP isa (copyOut slot 0 0) s fun t => ∃ M,
      CrtHalfReady g bs child slot (narrowWords (g.sourceLength j.succ) g.words) M t := by
  obtain ⟨shared, ready, modulus, odd, r2⟩ := h
  obtain ⟨member, _, _, sepCN, _, _, _⟩ := shared.child kind
  obtain ⟨_, le, _, _, _, _, half⟩ := shared.narrow_fits j prime
  refine WP.mono (crt_copyOut_ok s (shared.copyCtx kind ready le) (j := 0) (a := 0) (by decide) (by decide)) ?_
  rintro t ⟨readyT, _, outside, rest⟩
  have fitsC : arrAt g.words 8 ≤ 8 * workspaceWords g.words := shared.buffers.context.arraysFit
  have wsSmall : workspaceWords g.words ≤ 16 * 128 + 64 := by
    have : g.words ≤ 128 := (crt_width_valid shared.buffers.lengthValid).2.1
    simp only [workspaceWords]; omega
  have end0 := Nat.le_trans (array_end_le (w := g.words) (by decide : 0 < 8)) fitsC
  have frameC := outside_workspace outside (size := 8 * workspaceWords g.words) (by omega)
  have keeps := outside_array_prefix_keeps outside (by omega : 8 * workspaceWords g.words < 2 ^ 64)
    (by omega : 8 * narrowWords (g.sourceLength j.succ) g.words ≤ 8 * (g.words + 2))
  have layoutS := (shared.child kind).2.2.1
  have layoutT : CrtLayoutState child (workspaceWords g.words) g.words t.mem := by
    have kl := keeps_layout layoutS.layout (by rw [layoutS.width]; exact keeps)
    exact ⟨kl.2, kl.1.trans layoutS.width⟩
  have sharedT : CrtShared g bs t := by
    have f : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem :=
      frameC.mono (by simp)
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact shared.after_p f rest layoutT
    · exact shared.after_q f rest layoutT
  have sepC : ∀ r ∈ [(⟨State.addr child, 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sepCN.symm
  have eqN := shared.eq_of_frame shared.buffers.context.narrow shared.narrow_member
    (regions := [⟨State.addr child, 8 * workspaceWords g.words⟩]) (frameC.mono (by simp)) sepC
  have fitsN := ready.width ▸ ready.layout.2.2.1
  exact ⟨_, sharedT.copyCtx kind readyT le, (eqN.number fitsN (by decide)).trans modulus, odd,
    (eqN.number fitsN (by decide)).trans r2, half⟩

theorem crt_narrowReducedHalf_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot : Nat} {j i : Fin 6} {M : Nat}
    (h : CrtHalfReady g bs child slot (narrowWords (g.sourceLength j.succ) g.words) M s)
    (expI : i = 3 ∨ i = 4) :
    WP isa (reduceHalf slot 1) s (NarrowCopied g bs j i) := by
  obtain ⟨ctx, modulus, odd, r2, half⟩ := h
  have hi := i.isLt
  refine WP.mono (crt_reduceHalf_ok s ctx (j := 1) (by decide) half modulus odd r2) ?_
  rintro t ⟨readyT, modT, r2T, _, inputT, frameT, restT⟩
  have sharedT := ctx.shared.after_narrow (frameT.mono (by simp)) restT
  have length := ctx.shared.buffers.lengthValid.2
  refine ⟨sharedT, _, _, readyT, modT, odd, inputT, r2T, by have := sharedT.stack.nowrap; omega, by omega,
    sharedT.stack.read (by omega), sharedT.stack.read (by omega), sharedT.stack.pointer i, ?_,
    sharedT.buffers.source i.succ, (sharedT.buffers.sourceSeparate i.succ).sub_right
      (crt_region_sub_workspace sharedT.buffers.workspace sharedT.buffers.storageFits sharedT.narrow_member), ?_, ?_,
      table_fits ctx.le⟩
  · simpa only [show 56 + 8 * i.val + 4 = 60 + 8 * i.val by omega] using sharedT.stack.length i
  · rcases expI with rfl | rfl
    · exact ctx.shared.buffers.pPositive
    · exact ctx.shared.buffers.qPositive
  · rcases expI with rfl | rfl
    · change g.pLength < _; have := ctx.shared.buffers.pShort; omega
    · change g.qLength < _; have := ctx.shared.buffers.qShort; omega

theorem crt_narrowPowered_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot : Nat} {j i : Fin 6} (h : NarrowCopied g bs j i s) (kind : CrtChild g child slot) (prime : j = 1 ∨ j = 2)
    (kernel : WindowKernel := baselineWindowKernel) :
    WP isa ((narrowExpWith kernel.code) (56 + 8 * i.val)) s
      (CrtCopyCtx g bs child slot (narrowWords (g.sourceLength j.succ) g.words)) := by
  obtain ⟨shared, M, x, input⟩ := h
  obtain ⟨_, le, _, _, _, _, _⟩ := shared.narrow_fits j prime
  refine WP.mono ((crt_narrowExp_ok (kernel := kernel)) s input) ?_
  rintro t ⟨ready, _, frame, rest⟩
  exact (shared.after_narrow (frame.mono (by simp)) rest).copyCtx kind ready le

theorem crt_factorInput_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {i : Fin 6} :
    RelCT isa (fun s t =>
      CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs1 1) (bs1 i.succ) s ∧
      CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs2 1) (bs2 i.succ) t ∧ s.sp = t.sp)
      factorInput (fun _ _ => True) := by
  let L := fun (s : State) => LayoutFrameReady child (workspaceWords g.words) g.words s
  have source (s : State) {bs : Fin 7 → List Byte}
      (h : CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) s) :
      SavedOperand child g.input (workspaceWords g.words) g.length 56 12 (bs 1) s :=
    ⟨h.sources.stack.nowrap, ⟨h.sources.stack.readable.1, h.sources.stack.readable.2.1⟩, h.sources.stack.separate,
      by decide, by decide, h.sources.stack.input, h.sources.stack.inputCount, h.sources.input,
      h.sources.inputSeparate⟩
  have load := (savedOperandLayout_ct (base := child) (len := workspaceWords g.words) (w := g.words)
    (ps := 56) (cs := 12) (by decide : 1 < 8)).mono
    (P' := fun (s t : State) =>
      CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs1 1) (bs1 i.succ) s ∧
      CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs2 1) (bs2 i.succ) t ∧ s.sp = t.sp)
    (fun s t h => ⟨⟨h.1.accepted.toLayoutFrameReady, source s h.1⟩, ⟨h.2.1.accepted.toLayoutFrameReady, source t h.2.1⟩,
      h.2.2⟩) (fun _ _ _ => trivial)
  have loadWP (s : State) {bs : Fin 7 → List Byte}
      (h : CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) s) :
      WP isa (savedOperand 1 56 12) s L :=
    (savedOperandLayout_ok s h.accepted.toLayoutFrameReady (source s h) (by decide : 1 < 8)
      h.sources.inputPositive h.sources.inputFits).mono fun _ k => k.1
  have size (s : State) (h : L s) : 256 ≤ 8 * workspaceWords g.words := by
    have := h.width ▸ h.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  have clear (o : Nat) (ho : o < 8) :
      RelCT isa (fun s t => L s ∧ L t ∧ s.sp = t.sp) (clearOperandBuffer (64 + 8 * o)) (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    have sz := size s h.1
    have input (s' : State) (h' : L s') : ClearOperandBufferInput child (child + BitVec.ofNat 32 (arrAt g.words o))
        (8 * workspaceWords g.words) (64 + 8 * o) g.words s' := by
      have header := nativeHeader_of_layout s'.mem child h'.workspace.nowrap (Nat.le_refl _) h'.layout
      rw [h'.width] at header
      exact ⟨h'.workspace, h'.ptr, header.count, header.array o ho⟩
    exact clearOperandBuffer_ct (by omega) (by omega) (by omega) s t tr1 tr2 u w
      ⟨input s h.1, input t h.2.1, h.2.2⟩ e1 e2
  have clearWP (s : State) (h : L s) : WP isa (clearOperandBuffer (64 + 8 * 0)) s L :=
    (clearLayout_ok s h (o := 0) (by decide)).mono fun _ k => k.1
  rw [factorInput]
  exact crt_seq_ct load (fun s h => loadWP s h) (fun s h => loadWP s h)
    (crt_seq_ct (clear 0 (by decide)) (fun s h => clearWP s h) (fun s h => clearWP s h) (clear 6 (by decide)))

theorem crt_narrowPower_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (kind : CrtChild g child slot) (j i : Fin 6) (pair : (j = 1 ∧ i = 3) ∨ (j = 2 ∧ i = 4)) (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t =>
      (CrtShared g bs1 s ∧ CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs1 1) (bs1 i.succ) s ∧
        numAt s.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs1 j.succ)) ∧
      (CrtShared g bs2 t ∧ CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs2 1) (bs2 i.succ) t ∧
        numAt t.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs2 j.succ)) ∧ s.sp = t.sp)
      ((narrowPowerWith kernel.code) slot (56 + 8 * j.val) (56 + 8 * i.val)) (fun _ _ => True) := by
  have primeJ : j = 1 ∨ j = 2 := by rcases pair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  have expI : i = 3 ∨ i = 4 := by rcases pair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  intro s t tr1 tr2 u w h e1 e2
  obtain ⟨two, le, _, _, _, arrays, _⟩ := h.1.1.narrow_fits j primeJ
  have words : g.words ≤ 128 := (crt_width_valid h.1.1.buffers.lengthValid).2.1
  have fitV : arrAt (narrowWords (g.sourceLength j.succ) g.words) 3 + 32 ≤ 8 * workspaceWords g.words := by
    have := Nat.le_trans (array_end_le (w := narrowWords (g.sourceLength j.succ) g.words) (by decide : 3 < 8)) arrays
    omega
  have inputCT := (crt_factorInput_ct (g := g) (bs1 := bs1) (bs2 := bs2) (child := child) (i := i)).mono
    (P' := fun (s t : State) =>
      (CrtShared g bs1 s ∧ CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs1 1) (bs1 i.succ) s ∧
        numAt s.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs1 j.succ)) ∧
      (CrtShared g bs2 t ∧ CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs2 1) (bs2 i.succ) t ∧
        numAt t.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs2 j.succ)) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.2.1, h.2.1.2.1, h.2.2⟩) (fun _ _ _ => trivial)
  have enterCT := (crt_enterNarrow_ct (g := g) (bs1 := bs1) (bs2 := bs2) j primeJ).mono
    (P' := fun (s t : State) => NarrowAccepted g bs1 j s ∧ NarrowAccepted g bs2 j t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have primeCT := (crt_narrowPrime_ct (pb1 := bs1 j.succ) (pb2 := bs2 j.succ) (by omega)).mono
    (P' := fun (s t : State) => NarrowEntered g bs1 j s ∧ NarrowEntered g bs2 j t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.primeInput primeJ, h.2.1.primeInput primeJ, h.2.2⟩) (fun _ _ _ => trivial)
  have backCT := (crt_copyOut_ct (bs1 := bs1) (bs2 := bs2) (child := child) (slot := slot)
    (v := narrowWords (g.sourceLength j.succ) g.words) (j := 0) (a := 0) (by decide) (by decide)).mono
    (P' := fun (s t : State) => NarrowPrepared g bs1 j s ∧ NarrowPrepared g bs2 j t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1.copyCtx kind h.1.2.1 le, h.2.1.1.copyCtx kind h.2.1.2.1 le, h.2.2⟩) (fun _ _ _ => trivial)
  have halfCT : RelCT isa (fun s t =>
      (∃ M, CrtHalfReady g bs1 child slot (narrowWords (g.sourceLength j.succ) g.words) M s) ∧
      (∃ M, CrtHalfReady g bs2 child slot (narrowWords (g.sourceLength j.succ) g.words) M t) ∧ s.sp = t.sp)
      (reduceHalf slot 1) (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    obtain ⟨⟨M1, h1⟩, ⟨M2, h2⟩, sp⟩ := h
    exact crt_reduceHalf_ct (by decide) s t tr1 tr2 u w ⟨h1, h2, sp⟩ e1 e2
  have expCT : RelCT isa (fun s t => NarrowCopied g bs1 j i s ∧ NarrowCopied g bs2 j i t ∧ s.sp = t.sp)
      ((narrowExpWith kernel.code) (56 + 8 * i.val)) (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    obtain ⟨⟨_, M1, x1, h1⟩, ⟨_, M2, x2, h2⟩, sp⟩ := h
    exact (crt_narrowExp_ct (kernel := kernel)) fitV (table_fits le) s t tr1 tr2 u w ⟨h1, h2, sp⟩ e1 e2
  have resultCT := crt_copyOut_ct (g := g) (bs1 := bs1) (bs2 := bs2) (child := child) (slot := slot)
    (v := narrowWords (g.sourceLength j.succ) g.words) (j := 6) (a := 6) (by decide) (by decide)
  rw [narrowPowerWith] at e1 e2
  exact (crt_seq_ct inputCT (fun s h => crt_narrowAccepted_ready s h.1 kind h.2.1 h.2.2)
      (fun s h => crt_narrowAccepted_ready s h.1 kind h.2.1 h.2.2)
    (crt_seq_ct enterCT (fun s h => crt_narrowEntered_ready s h primeJ)
      (fun s h => crt_narrowEntered_ready s h primeJ)
    (crt_seq_ct primeCT (fun s h => crt_narrowPrepared_ready s h primeJ)
      (fun s h => crt_narrowPrepared_ready s h primeJ)
    (crt_seq_ct backCT (fun s h => crt_narrowCopiedBack_ready s h kind primeJ)
      (fun s h => crt_narrowCopiedBack_ready s h kind primeJ)
    (crt_seq_ct halfCT (fun s h => by obtain ⟨M, h⟩ := h; exact crt_narrowReducedHalf_ready s h expI)
      (fun s h => by obtain ⟨M, h⟩ := h; exact crt_narrowReducedHalf_ready s h expI)
    (crt_seq_ct expCT (fun s h => (crt_narrowPowered_ready (kernel := kernel)) s h kind primeJ)
      (fun s h => (crt_narrowPowered_ready (kernel := kernel)) s h kind primeJ)
      resultCT)))))) s t tr1 tr2 u w h e1 e2

end VG.Proof.Bignum.Arm
