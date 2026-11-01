module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowReduce
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowExp

import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnterCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowInputCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowResultCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowInput
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

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtNarrowReduceCT.lean`, which only this module imported.
section

/-! # Reducing the input modulo a factor hides the factor, the input and acceptance -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)

/-- A prepared full-width factor workspace, with its constants, for some factor. -/
def CrtReduceReady (base : BitVec 32) (len w : Nat) (one : Bool) (s : State) : Prop :=
  ∃ M, ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M ∧ M % 2 = 1 ∧
    numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧ (one → numAt s.mem (State.addr base) w 7 = 1)

theorem crt_narrowReduce_ct {base xp ep : BitVec 32} {len w k eLen slot : Nat} {xb1 xb2 eb1 eb2 : List Byte}
    (countFits : 128 * w < 2 ^ 32) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => CrtPrimePowerInput base xp ep len w k eLen slot xb1 eb1 s ∧
      CrtPrimePowerInput base xp ep len w k eLen slot xb2 eb2 t ∧ s.sp = t.sp) reducePrime (fun _ _ => True) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega
  let Prepared := fun (xb eb : List Byte) (s : State) =>
    ∃ M, CrtPreparedPower base xp ep len w k eLen slot M xb eb s
  have prepare : RelCT isa (fun s t => CrtPrimePowerInput base xp ep len w k eLen slot xb1 eb1 s ∧
      CrtPrimePowerInput base xp ep len w k eLen slot xb2 eb2 t ∧ s.sp = t.sp)
      prepareAcceptedPrime (fun _ _ => True) :=
    (prepareAcceptedPrime_ct countFits).mono
      (fun _ _ h => ⟨h.1.accepted, h.2.1.accepted, h.2.2⟩) (fun _ _ _ => trivial)
  have prepareWP (s : State) {xb eb : List Byte}
      (h : CrtPrimePowerInput base xp ep len w k eLen slot xb eb s) : WP isa prepareAcceptedPrime s (Prepared xb eb) :=
    (crt_primePower_prepare s h countFits).mono (fun _ j => ⟨_, j.1⟩)
  -- The input.
  have source (s : State) {xb eb : List Byte} {M : Nat} (h : CrtPreparedPower base xp ep len w k eLen slot M xb eb s) :
      SavedOperand base xp len k 56 12 xb s :=
    ⟨h.sources.stack.nowrap, ⟨h.sources.stack.readable.1, h.sources.stack.readable.2.1⟩, h.sources.stack.separate,
      by decide, by decide, h.sources.stack.input, h.sources.stack.inputCount, h.sources.input, h.sources.inputSeparate⟩
  have load : RelCT isa (fun s t => Prepared xb1 eb1 s ∧ Prepared xb2 eb2 t ∧ s.sp = t.sp)
      (savedOperand 1 56 12) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨⟨M1, h1⟩, ⟨M2, h2⟩, sp⟩ := h
    exact (savedOperand_ct (by decide : 1 < 8)) s t tr1 tr2 u v
      ⟨⟨h1.ready, source s h1⟩, ⟨h2.ready, source t h2⟩, sp⟩ e1 e2
  have loadWP (s : State) {xb eb : List Byte} (h : Prepared xb eb s) :
      WP isa (savedOperand 1 56 12) s (CrtReduceReady base len w false) := by
    obtain ⟨M, h⟩ := h
    refine WP.mono (savedOperand_ok s h.ready (source s h) (by decide : 1 < 8) (by decide)
      h.sources.inputPositive h.sources.inputFits) ?_
    rintro t ⟨ready, _, keeps, _, _⟩
    have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
    exact ⟨M, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus, h.odd,
      (keeps_array_num keeps fits op4 (by decide)).trans h.r2, by simp⟩
  -- The constant one.
  have one : RelCT isa (fun s t => CrtReduceReady base len w false s ∧ CrtReduceReady base len w false t ∧ s.sp = t.sp)
      (smallConst 7 1) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨⟨_, h1, _⟩, ⟨_, h2, _⟩, sp⟩ := h
    exact (smallConst_ct (base := base) (len := len) (w := w) (o := 7) 1 (by decide) (by decide) (by decide))
      s t tr1 tr2 u v ⟨h1, h2, sp⟩ e1 e2
  have oneWP (s : State) (h : CrtReduceReady base len w false s) :
      WP isa (smallConst 7 1) s (CrtReduceReady base len w true) := by
    obtain ⟨M, ready, modulus, odd, r2, _⟩ := h
    refine WP.mono (smallConst_ok s (o := 7) 1 ready (by decide) (by decide) (by decide) (by decide)) ?_
    rintro t ⟨readyT, oneT, _, keeps, _, _⟩
    have fits : arrAt w 8 ≤ 8 * len := ready.width ▸ ready.layout.2.2.1
    exact ⟨M, readyT, (keeps_array_num keeps fits op0 (by decide)).trans modulus, odd,
      (keeps_array_num keeps fits op4 (by decide)).trans r2, fun _ => oneT⟩
  -- The reduction.
  have reduceReady (s : State) (h : CrtReduceReady base len w true s) : ReduceOperandReady base len w s := by
    obtain ⟨M, ready, modulus, _, r2, one⟩ := h
    have positive := ready.modulus
    refine ⟨ready, ?_, ?_⟩
    · rw [r2, modulus]; rw [modulus] at positive; exact Nat.mod_lt _ (by omega)
    · rw [one rfl]; exact positive
  have reduce : RelCT isa (fun s t => CrtReduceReady base len w true s ∧ CrtReduceReady base len w true t ∧ s.sp = t.sp)
      (reduceOperand 1) (fun _ _ => True) :=
    (reduceOperand_ct op1 (by decide) (by decide) fit).mono
      (fun s t h => ⟨reduceReady s h.1, reduceReady t h.2.1, h.2.2⟩) (fun _ _ _ => trivial)
  have reduceWP (s : State) (h : CrtReduceReady base len w true s) :
      WP isa (reduceOperand 1) s (ArithmeticReady base len w) := by
    obtain ⟨M, ready, modulus, odd, r2, one⟩ := h
    exact (reduceOperand_ok s ready op1 (by decide) (by decide) modulus odd r2 (one rfl)).mono (fun _ j => j.1)
  have clear : RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (clearOperandBuffer (64 + 8 * 6)) (fun _ _ => True) :=
    clearArrayWide_ct (by decide) size
  have midWP (s : State) {xb eb : List Byte} (h : Prepared xb eb s) :
      WP isa (.seq (savedOperand 1 56 12) (.seq (smallConst 7 1) (reduceOperand 1))) s (ArithmeticReady base len w) :=
    WP.seq_iff.mpr ((loadWP s h).mono fun _ hu => WP.seq_iff.mpr ((oneWP _ hu).mono fun _ hz => reduceWP _ hz))
  rw [reducePrime, reduceInput]
  exact crt_seq_ct prepare (fun s h => prepareWP s h) (fun s h => prepareWP s h)
    (crt_seq_ct (crt_seq_ct load (fun s h => loadWP s h) (fun s h => loadWP s h) (crt_seq_ct one oneWP oneWP reduce))
      (fun s h => midWP s h) (fun s h => midWP s h) clear)

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtNarrowPrimeCT.lean`, which only this module imported.
section

/-! # Preparing the factor in the narrow workspace hides the factor and acceptance -/

section

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

/-- The input reduced modulo the factor at the modulus width. -/
def NarrowReduced (s : State) : Prop :=
  CrtShared g bs s ∧ (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1 ∧
    ((s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≠ 0 →
      1 < Spec.Rsa.os2ip (bs j.succ) ∧ Spec.Rsa.os2ip (bs j.succ) % 2 = 1) ∧
    CrtReducedState child (workspaceWords g.words) g.words (narrowM s (bs j.succ)) (Spec.Rsa.os2ip (bs 1)) s.mem

/-- The narrow workspace selected and set up. -/
def NarrowEntered (s : State) : Prop :=
  NarrowReduced g bs child j s ∧
    LayoutFrameReady (crtN g.base g.words) (workspaceWords g.words) (narrowWords (g.sourceLength j.succ)) s

/-- The factor prepared in the narrow workspace. -/
def NarrowPrepared (s : State) : Prop :=
  CrtShared g bs s ∧
    ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) (narrowWords (g.sourceLength j.succ)) s ∧
    numAt s.mem (State.addr (crtN g.base g.words)) (narrowWords (g.sourceLength j.succ)) 0 = narrowM s (bs j.succ) ∧
    narrowM s (bs j.succ) % 2 = 1 ∧
    numAt s.mem (State.addr (crtN g.base g.words)) (narrowWords (g.sourceLength j.succ)) 4 =
      2 ^ (128 * narrowWords (g.sourceLength j.succ)) % narrowM s (bs j.succ) ∧
    CrtReducedState child (workspaceWords g.words) g.words (narrowM s (bs j.succ)) (Spec.Rsa.os2ip (bs 1)) s.mem

/-- The reduced input in the narrow workspace, ready for the exponent `i`. -/
def NarrowCopied (i : Fin 6) (s : State) : Prop :=
  CrtShared g bs s ∧ ∃ M x, NarrowExpInput (crtN g.base g.words) (g.source i.succ) (workspaceWords g.words)
    (narrowWords (g.sourceLength j.succ)) M x (g.sourceLength i.succ) (56 + 8 * i.val) (bs i.succ) s

end

theorem NarrowEntered.primeInput {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {j : Fin 6} (h : NarrowEntered g bs child j s) (prime : j = 1 ∨ j = 2) :
    NarrowPrimeInput (crtN g.base g.words) (g.source j.succ) (workspaceWords g.words)
      (narrowWords (g.sourceLength j.succ)) (g.sourceLength j.succ) (56 + 8 * j.val) (bs j.succ) s := by
  obtain ⟨⟨shared, bit, valid, _⟩, selected⟩ := h
  obtain ⟨_, _, kfit, kpos, _, _⟩ := shared.narrow_fits j prime
  have hj := j.isLt
  exact ⟨selected,
    by simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega] using shared.savedOperand j shared.narrow_member,
    kpos, kfit, by have := shared.stack.nowrap; omega, shared.stack.read (by decide), bit, valid⟩

theorem crt_narrowReduced_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot : Nat} {j i : Fin 6} (h : CrtShared g bs s) (kind : CrtChild g child slot)
    (input : CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words g.length
      (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) s)
    (prime : numAt s.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs j.succ)) :
    WP isa reducePrime s (NarrowReduced g bs child j) := by
  obtain ⟨member, _, _, _, _, _, _⟩ := h.child kind
  have words := (crt_width_valid h.buffers.lengthValid).2.1
  refine WP.mono (crt_narrowReduce_ok s input (by change 128 * Spec.Rsa.modulusWords g.length < _; omega)) ?_
  rintro u ⟨readyU, reducedU, frameU, restU⟩
  have shared : CrtShared g bs u := by
    have f : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem u.mem :=
      frameU.mono (by simp)
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h.after_p f restU ⟨readyU.layout, readyU.width⟩
    · exact h.after_q f restU ⟨readyU.layout, readyU.width⟩
  have flag := h.acceptance_after_workspace member frameU restU
  refine ⟨shared, by rw [flag]; exact input.accepted.bit, by rw [flag, ← prime]; exact input.accepted.valid, ?_⟩
  unfold narrowM
  rw [flag, ← prime]
  exact reducedU

theorem crt_narrowEntered_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot : Nat} {j : Fin 6} (h : NarrowReduced g bs child j s) (kind : CrtChild g child slot) (prime : j = 1 ∨ j = 2) :
    WP isa (enterNarrow (56 + 8 * j.val + 4)) s (NarrowEntered g bs child j) := by
  obtain ⟨shared, bit, valid, reduced⟩ := h
  obtain ⟨member, ws, _, sepCN, _, _, _⟩ := shared.child kind
  refine WP.mono (crt_enterNarrow_ok s shared j prime) ?_
  rintro t ⟨sharedT, selected, flag, frame, rest⟩
  have eq := shared.eq_of_frame ws member (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩])
    (frame.mono (by simp)) (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sepCN)
  refine ⟨⟨sharedT, by rw [flag]; exact bit, by rw [flag]; exact valid, ?_⟩, selected⟩
  unfold narrowM
  rw [flag]
  exact reduced.congr eq

theorem crt_narrowPrepared_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot : Nat} {j : Fin 6} (h : NarrowEntered g bs child j s) (kind : CrtChild g child slot) (prime : j = 1 ∨ j = 2) :
    WP isa (narrowPrime (56 + 8 * j.val)) s (NarrowPrepared g bs child j) := by
  have shared := h.1.1
  obtain ⟨member, ws, _, sepCN, _, _, _⟩ := shared.child kind
  obtain ⟨_, le, _, _, _, _⟩ := shared.narrow_fits j prime
  have words := (crt_width_valid shared.buffers.lengthValid).2.1
  change _ ≤ Spec.Rsa.modulusWords g.length at le
  refine WP.mono (crt_narrowPrime_ok s (h.primeInput prime) (by omega)) ?_
  rintro t ⟨ready, modulus, odd, r2, flag, frame, rest⟩
  have eq := shared.eq_of_frame ws member (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩])
    (frame.mono (by simp)) (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sepCN)
  have m : narrowM t (bs j.succ) = narrowM s (bs j.succ) := by unfold narrowM; rw [flag]
  unfold NarrowPrepared
  rw [m]
  exact ⟨shared.after_narrow (frame.mono (by simp)) rest, ready, modulus, odd, r2, h.1.2.2.2.congr eq⟩

theorem crt_narrowCopied_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot : Nat} {j i : Fin 6} (h : NarrowPrepared g bs child j s) (kind : CrtChild g child slot)
    (pair : (j = 1 ∧ i = 3) ∨ (j = 2 ∧ i = 4)) :
    WP isa (narrowInput slot) s (NarrowCopied g bs j i) := by
  obtain ⟨shared, ready, modulus, odd, r2, reduced⟩ := h
  have primeJ : j = 1 ∨ j = 2 := by rcases pair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  have expI : i = 3 ∨ i = 4 := by rcases pair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  obtain ⟨_, ws, _, sepCN, slotFit, hs, link⟩ := shared.child kind
  obtain ⟨_, le, _, _, _, _⟩ := shared.narrow_fits j primeJ
  have hi := i.isLt
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (crt_narrowInput_ok s shared ready ws sepCN slotFit hs link reduced modulus le) ?_
  rintro t ⟨readyT, inputT, keepsT, frameT, restT⟩
  have fitsN := ready.width ▸ ready.layout.2.2.1
  have sharedT := shared.after_narrow (frameT.mono (by simp)) restT
  have length := shared.buffers.lengthValid.2
  refine ⟨sharedT, _, _, readyT, (keeps_array_num keepsT fitsN op0 (by decide)).trans modulus, odd, inputT,
    (keeps_array_num keepsT fitsN op4 (by decide)).trans r2, by have := sharedT.stack.nowrap; omega, by omega,
    sharedT.stack.read (by omega), sharedT.stack.read (by omega), sharedT.stack.pointer i, ?_,
    sharedT.buffers.source i.succ, (sharedT.buffers.sourceSeparate i.succ).sub_right
      (crt_region_sub_workspace sharedT.buffers.workspace sharedT.buffers.storageFits sharedT.narrow_member), ?_, ?_,
      table_fits le⟩
  · simpa only [show 56 + 8 * i.val + 4 = 60 + 8 * i.val by omega] using sharedT.stack.length i
  · rcases expI with rfl | rfl
    · exact shared.buffers.pPositive
    · exact shared.buffers.qPositive
  · rcases expI with rfl | rfl
    · change g.pLength < _; have := shared.buffers.pShort; omega
    · change g.qLength < _; have := shared.buffers.qShort; omega

theorem crt_narrowPowered_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {j i : Fin 6}
    (h : NarrowCopied g bs j i s) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa ((narrowExpWith kernel.code) (56 + 8 * i.val)) s fun t => CrtShared g bs t ∧
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) (narrowWords (g.sourceLength j.succ)) t := by
  obtain ⟨shared, M, x, input⟩ := h
  refine WP.mono ((crt_narrowExp_ok (kernel := kernel)) s input) ?_
  rintro t ⟨ready, _, frame, rest⟩
  exact ⟨shared.after_narrow (frame.mono (by simp)) rest, ready⟩

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
  intro s t tr1 tr2 u w h e1 e2
  obtain ⟨two, le, _, _, _, arrays⟩ := h.1.1.narrow_fits j primeJ
  have words := (crt_width_valid h.1.1.buffers.lengthValid).2.1
  have fitW : arrAt g.words 3 + 32 ≤ 8 * workspaceWords g.words := by
    have := Nat.le_trans (array_end_le (w := g.words) (by decide : 3 < 8)) h.1.1.buffers.context.arraysFit
    have := h.1.1.buffers.context.width
    omega
  have fitV : arrAt (narrowWords (g.sourceLength j.succ)) 3 + 32 ≤ 8 * workspaceWords g.words := by
    have := Nat.le_trans (array_end_le (w := narrowWords (g.sourceLength j.succ)) (by decide : 3 < 8)) arrays
    omega
  change _ ≤ Spec.Rsa.modulusWords g.length at le
  have reduceCT := (crt_narrowReduce_ct (base := child) (xp := g.input) (ep := g.source i.succ)
    (len := workspaceWords g.words) (w := g.words) (k := g.length) (eLen := g.sourceLength i.succ)
    (slot := 56 + 8 * i.val) (xb1 := bs1 1) (xb2 := bs2 1) (eb1 := bs1 i.succ) (eb2 := bs2 i.succ)
    (by change 128 * Spec.Rsa.modulusWords g.length < _; omega) fitW).mono
    (P' := fun (s t : State) =>
      (CrtShared g bs1 s ∧ CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs1 1) (bs1 i.succ) s ∧
        numAt s.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs1 j.succ)) ∧
      (CrtShared g bs2 t ∧ CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
        g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs2 1) (bs2 i.succ) t ∧
        numAt t.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs2 j.succ)) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.2.1, h.2.1.2.1, h.2.2⟩) (fun _ _ _ => trivial)
  have enterCT := (crt_enterNarrow_ct (g := g) (bs1 := bs1) (bs2 := bs2) j primeJ).mono
    (P' := fun (s t : State) => NarrowReduced g bs1 child j s ∧ NarrowReduced g bs2 child j t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have primeCT := (crt_narrowPrime_ct (pb1 := bs1 j.succ) (pb2 := bs2 j.succ) (by omega)).mono
    (P' := fun (s t : State) => NarrowEntered g bs1 child j s ∧ NarrowEntered g bs2 child j t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.primeInput primeJ, h.2.1.primeInput primeJ, h.2.2⟩) (fun _ _ _ => trivial)
  have inputCT := (crt_narrowInput_ct (bs1 := bs1) (bs2 := bs2) (v := narrowWords (g.sourceLength j.succ)) kind).mono
    (P' := fun (s t : State) => NarrowPrepared g bs1 child j s ∧ NarrowPrepared g bs2 child j t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1.1, h.2.1.2.1⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have expCT : RelCT isa (fun s t => NarrowCopied g bs1 j i s ∧ NarrowCopied g bs2 j i t ∧ s.sp = t.sp)
      ((narrowExpWith kernel.code) (56 + 8 * i.val)) (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    obtain ⟨⟨_, M1, x1, h1⟩, ⟨_, M2, x2, h2⟩, sp⟩ := h
    exact (crt_narrowExp_ct (kernel := kernel)) fitV (table_fits le) s t tr1 tr2 u w ⟨h1, h2, sp⟩ e1 e2
  have resultCT := crt_narrowResult_ct (bs1 := bs1) (bs2 := bs2) kind le
  rw [narrowPowerWith] at e1 e2
  exact (crt_seq_ct reduceCT (fun s h => crt_narrowReduced_ready s h.1 kind h.2.1 h.2.2)
      (fun s h => crt_narrowReduced_ready s h.1 kind h.2.1 h.2.2)
    (crt_seq_ct enterCT (fun s h => crt_narrowEntered_ready s h kind primeJ)
      (fun s h => crt_narrowEntered_ready s h kind primeJ)
    (crt_seq_ct primeCT (fun s h => crt_narrowPrepared_ready s h kind primeJ)
      (fun s h => crt_narrowPrepared_ready s h kind primeJ)
    (crt_seq_ct inputCT (fun s h => crt_narrowCopied_ready s h kind pair)
      (fun s h => crt_narrowCopied_ready s h kind pair)
    (crt_seq_ct expCT (fun s h => (crt_narrowPowered_ready (kernel := kernel)) s h) (fun s h => (crt_narrowPowered_ready (kernel := kernel)) s h)
      resultCT))))) s t tr1 tr2 u w h e1 e2

end VG.Proof.Bignum.Arm
