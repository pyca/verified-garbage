module

public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPrepare
import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationFacts
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
import VerifiedGarbage.Proof.Bignum.Arm.PdImport
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Bignum.Arm.PdImport
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment

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
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
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
    omega
  have widthPositive := p.width.1
  have originalFit := environment.fit
  have address : State.addr pp = off (State.addr p.cachedContext) 24 := VG.Arm.addr_add (by omega)
  have ppFit : pp.toNat + 16 * p.w ≤ 2 ^ 32 := by
    simp only [pp, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : p.cachedContext.toNat + 24 < 2 ^ 32)]
    omega
  have readyU : LayoutFrameReady p.base p.len p.w u :=
    ⟨⟨prepared.workspace, prepared.layout, prepared.width, prepared.ptr⟩,
      prepared.stackRead, prepared.stackSep, prepared.saved⟩
  have readyV := readyU.of_mem memV restV ((restV.gpr .r0 (by simp)).trans prepared.ptr)
  have regionSub : (⟨State.addr pp, 16 * p.w⟩ : Region).Sub (cachedRegion p) := by
    rw [address]
    exact Offset.sub_base _ (by omega)
  have importInput : PdImportInput p.base pp p.len p.w v :=
    ⟨readyV, ppFit, by
      rw [restV.rd, restV.wr, address]
      exact CallLay.inRegions_sub environmentU.readable (by omega) (by omega),
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
