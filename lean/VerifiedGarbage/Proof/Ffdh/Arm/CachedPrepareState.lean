module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedPrepare
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
import VerifiedGarbage.Proof.Bignum.Arm.PdImport
import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationFacts

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
    omega
  have widthPositive := p.width.1
  have originalFit := environment.fit
  have address : State.addr pp = off (State.addr p.cachedContext) 24 := VG.Arm.addr_add (by omega)
  have ppFit : pp.toNat + 16 * p.w ≤ 2 ^ 32 := by
    simp only [pp, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : p.cachedContext.toNat + 24 < 2 ^ 32)]
    omega
  have regionSub : (⟨State.addr pp, 16 * p.w⟩ : Region).Sub (cachedRegion p) := by
    rw [address]
    exact Offset.sub_base _ (by omega)
  exact ⟨ready, ppFit, by
    rw [address]
    exact CallLay.inRegions_sub environment.readable (by omega) (by omega),
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
    omega
  have widthPositive := p.width.1
  have fit := h.environment.fit
  have address : State.addr (p.cachedContext + BitVec.ofNat 32 24) = off (State.addr p.cachedContext) 24 :=
    VG.Arm.addr_add (by omega)
  rw [address] at modulus
  have value : (s.mem.read (off (State.addr p.cachedContext) 24) (8 * p.w)).toNat = p.P := by
    simpa only [VG.Proof.Mont.off, BitVec.ofNat_eq_ofNat] using h.environment.montgomeryReads.1
  rw [value] at modulus
  have facts := VG.Proof.Bignum.valid_facts (VG.Proof.Ffdh.domainValid_mod h.environment.valid) p.minLength
  change p.P % 2 = 1 ∧ 1 < p.P ∧ _ at facts
  exact ⟨⟨ready.workspace, ready.layout, ready.width, ready.ptr, ready.stackRead, ready.stackSep, ready.saved⟩,
    by rw [modulus]; exact facts.2.1, by rw [modulus]; exact facts.1⟩

end VG.Proof.Ffdh.Arm
