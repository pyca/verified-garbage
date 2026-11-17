module

public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPrepare
public import VerifiedGarbage.Proof.Bignum.Arm.PdImport
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationFacts
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Impl.Bignum.Arm.PdImport
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! ### `Ffdh.Arm.CachedPrepare`, which this module and modules that import it used -/

section

/-! Reuse RSA's packed precomputation importer for a cached FFDH domain. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem cachedPrepareSource_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (h52 : 52 ∈ slots) :
    WP isa (.block VG.Impl.Ffdh.Arm.CachedPrepare.source) s fun t =>
      (t.gpr .r4 = p.cachedContext + BitVec.ofNat 32 24 ∧ t.mem = s.mem) ∧ Rest [.r4] s t := by
  have addr52 : State.addr (s.sp + BitVec.ofNat 32 52) = off (State.addr s.sp) 52 :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega_using [this])
  refine withRest_all [.r4] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.CachedPrepare.source
  ffrun [addr52, h.locals.read (d := 52) (by decide), h.saved 52 h52, Inputs.slotValue]
  rfl

theorem cachedPrepareBody_ok (s : State) {p : Inputs} {slots : List Nat}
    (input : PrepareInput p.base p.domain p.len p.k s)
    (context : Context p slots s) (environment : CachedGenerationContext p s)
    (h52 : 52 ∈ slots) (stable : stableSlots slots = true) :
    WP isa VG.Impl.Ffdh.Arm.CachedPrepare.body s fun t =>
      Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CachedPrepare.body, WP.seq_iff]
  refine WP.mono (prepare_input s input) ?_
  rintro u ⟨prepared, frameU, restU⟩
  have contextU := context.after_workspace frameU restU prepared.ptr (fun d hd => (stableSlots_at stable hd).1)
  have environmentU := environment.after (frameU.mono (by simp [keyCallWrites, keyWrites])) restU
  rw [WP.seq_iff]
  refine WP.mono (cachedPrepareSource_ok u contextU h52) ?_
  rintro v ⟨⟨source, memV⟩, restV⟩
  let pp := p.cachedContext + BitVec.ofNat 32 24
  have count : 3 + 2 * p.w ≤ p.cachedWords := by
    rw [environment.canonical.1, Spec.Ffdh.generationPrecomputedWords,
      Spec.Rsa.FixedBaseComb.precomputedWords, Spec.Rsa.precomputedWords, Inputs.w]
    omega_using []
  have widthPositive := p.width.1
  have originalFit := environment.fit
  have address : State.addr pp = off (State.addr p.cachedContext) 24 := VG.Arm.addr_add (by omega_using [count, widthPositive, originalFit])
  have ppFit : pp.toNat + 16 * p.w ≤ 2 ^ 32 := by
    simp only [pp, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [count, widthPositive, originalFit] : p.cachedContext.toNat + 24 < 2 ^ 32)]
    omega_using [count, originalFit]
  have readyU : LayoutFrameReady p.base p.len p.w u :=
    ⟨⟨prepared.workspace, prepared.layout, prepared.width, prepared.ptr⟩,
      prepared.stackRead, prepared.stackSep, prepared.saved⟩
  have readyV := readyU.of_mem memV restV ((restV.gpr .r0 (by simp)).trans prepared.ptr)
  have regionSub : (⟨State.addr pp, 16 * p.w⟩ : Region).Sub (cachedRegion p) := by
    rw [address]
    exact Offset.sub_base _ (by omega_using [count])
  have importInput : PdImportInput p.base pp p.len p.w v :=
    ⟨readyV, ppFit, by
      rw [restV.rd, restV.wr, address]
      exact CallLay.inRegions_sub environmentU.readable (by omega_using [count]) (by omega_using [originalFit]),
      ((environmentU.separate _ (by simp [keyCallWrites, keyWrites])).sub_left regionSub).symm,
      source⟩
  rw [WP.seq_iff]
  refine WP.mono (pdImport_ok v importInput) ?_
  rintro w ⟨readyW, modulus, r2, frameW, restW⟩
  have numbers := environmentU.montgomeryReads
  rw [memV, address] at modulus
  rw [memV, address] at r2
  have modulusP : numAt w.mem (State.addr p.base) p.w 0 = p.P :=
    modulus.trans (by simpa only [VG.Proof.Mont.off, BitVec.ofNat_eq_ofNat] using numbers.1)
  have r2P : numAt w.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P :=
    r2.trans (by simpa only [VG.Proof.Mont.off, VG.Proof.Bignum.off, BitVec.ofNat_eq_ofNat] using numbers.2)
  have valid := VG.Proof.Ffdh.domainValid_mod environment.valid
  have facts := VG.Proof.Bignum.valid_facts valid p.minLength
  change p.P % 2 = 1 ∧ 1 < p.P ∧ _ at facts
  refine WP.mono (precomputeInverse_r2_ok w readyW.workspace readyW.layout readyW.width readyW.ptr
    (by rw [modulusP]; exact facts.1) (by rw [modulusP]; exact facts.2.1)
    readyW.stackRead readyW.stackSep readyW.saved) ?_
  rintro t ⟨readyT, modulusT, frameT, restT, r2T⟩
  rw [modulusP] at modulusT
  rw [r2P] at r2T
  rw [memV] at frameW
  have frame := frameU.trans (frameW.trans frameT)
  have rest : Rest roundClobbers s t :=
    restU.trans ((restV.mono (by simp [roundClobbers])).trans (restW.trans restT))
  exact ⟨context.after_workspace frame rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1),
    readyT, modulusT, r2T, frame, rest⟩

end VG.Proof.Ffdh.Arm

end

end

/-! Public states connecting the existing RSA preparation and import phases. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CachedPrepareInitial (p : Inputs) (slots : List Nat) (s : State) : Prop where
  input : PrepareInput p.base p.domain p.len p.k s
  context : Context p slots s
  environment : CachedGenerationContext p s

structure CachedPrepareReady (p : Inputs) (slots : List Nat) (s : State) : Prop where
  ready : LayoutFrameReady p.base p.len p.w s
  context : Context p slots s
  environment : CachedGenerationContext p s

structure CachedPrepareLoaded (p : Inputs) (s : State) : Prop where
  input : PdImportInput p.base (p.cachedContext + BitVec.ofNat 32 24) p.len p.w s
  environment : CachedGenerationContext p s

theorem cachedPrepare_init_next (s : State) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h : CachedPrepareInitial p slots s) :
    WP isa VG.Impl.Bignum.Arm.PublicFn.prepare s (CachedPrepareReady p slots) := by
  refine WP.mono (prepare_input s h.input) ?_
  rintro t ⟨ready, frame, rest⟩
  exact ⟨⟨⟨ready.workspace, ready.layout, ready.width, ready.ptr⟩,
    ready.stackRead, ready.stackSep, ready.saved⟩,
    h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at stable hd).1),
    h.environment.after (frame.mono (by simp [keyCallWrites, keyWrites])) rest⟩

theorem cachedPrepare_import_input (s : State) {p : Inputs}
    (ready : LayoutFrameReady p.base p.len p.w s) (environment : CachedGenerationContext p s)
    (source : s.gpr .r4 = p.cachedContext + BitVec.ofNat 32 24) :
    PdImportInput p.base (p.cachedContext + BitVec.ofNat 32 24) p.len p.w s := by
  let pp := p.cachedContext + BitVec.ofNat 32 24
  have count : 3 + 2 * p.w ≤ p.cachedWords := by
    rw [environment.canonical.1, Spec.Ffdh.generationPrecomputedWords,
      Spec.Rsa.FixedBaseComb.precomputedWords, Spec.Rsa.precomputedWords, Inputs.w]
    omega_using []
  have widthPositive := p.width.1
  have originalFit := environment.fit
  have address : State.addr pp = off (State.addr p.cachedContext) 24 := VG.Arm.addr_add (by omega_using [count, widthPositive, originalFit])
  have ppFit : pp.toNat + 16 * p.w ≤ 2 ^ 32 := by
    simp only [pp, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [count, widthPositive, originalFit] : p.cachedContext.toNat + 24 < 2 ^ 32)]
    omega_using [count, originalFit]
  have regionSub : (⟨State.addr pp, 16 * p.w⟩ : Region).Sub (cachedRegion p) := by
    rw [address]
    exact Offset.sub_base _ (by omega_using [count])
  exact ⟨ready, ppFit, by
    rw [address]
    exact CallLay.inRegions_sub environment.readable (by omega_using [count]) (by omega_using [originalFit]),
    ((environment.separate _ (by simp [keyCallWrites, keyWrites])).sub_left regionSub).symm, source⟩

theorem cachedPrepare_source_next (s : State) {p : Inputs} {slots : List Nat}
    (h52 : 52 ∈ slots) (h : CachedPrepareReady p slots s) :
    WP isa (.block VG.Impl.Ffdh.Arm.CachedPrepare.source) s (CachedPrepareLoaded p) := by
  refine WP.mono (cachedPrepareSource_ok s h.context h52) ?_
  rintro t ⟨⟨source, mem⟩, rest⟩
  have ready := h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr)
  have frame : Frame (keyCallWrites p s) s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  have environment := h.environment.after frame (rest.mono (by simp [roundClobbers]))
  exact ⟨cachedPrepare_import_input t ready environment source, environment⟩

theorem cachedPrepare_import_next (s : State) {p : Inputs} (h : CachedPrepareLoaded p s) :
    WP isa VG.Impl.Bignum.Arm.pdImport s (PrecomputeModulus p.base p.len p.w) := by
  refine WP.mono (pdImport_ok s h.input) ?_
  rintro t ⟨ready, modulus, _r2, _frame, _rest⟩
  have count : 3 + 2 * p.w ≤ p.cachedWords := by
    rw [h.environment.canonical.1, Spec.Ffdh.generationPrecomputedWords,
      Spec.Rsa.FixedBaseComb.precomputedWords, Spec.Rsa.precomputedWords, Inputs.w]
    omega_using []
  have widthPositive := p.width.1
  have fit := h.environment.fit
  have address : State.addr (p.cachedContext + BitVec.ofNat 32 24) = off (State.addr p.cachedContext) 24 :=
    VG.Arm.addr_add (by omega_using [count, widthPositive, fit])
  rw [address] at modulus
  have value : (s.mem.read (off (State.addr p.cachedContext) 24) (8 * p.w)).toNat = p.P := by
    simpa only [VG.Proof.Mont.off, BitVec.ofNat_eq_ofNat] using h.environment.montgomeryReads.1
  rw [value] at modulus
  have facts := VG.Proof.Bignum.valid_facts (VG.Proof.Ffdh.domainValid_mod h.environment.valid) p.minLength
  change p.P % 2 = 1 ∧ 1 < p.P ∧ _ at facts
  exact ⟨⟨ready.workspace, ready.layout, ready.width, ready.ptr, ready.stackRead, ready.stackSep, ready.saved⟩,
    by rw [modulus]; exact facts.2.1, by rw [modulus]; exact facts.1⟩

end VG.Proof.Ffdh.Arm
