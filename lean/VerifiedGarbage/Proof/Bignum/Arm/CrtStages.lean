module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Bignum.Arm.CrtValidateProduct
import VerifiedGarbage.Impl.Bignum.Arm.MergeAcceptance
public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationGeometry
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceLayout
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
import VerifiedGarbage.Impl.Bignum.Arm.SavedOperand
public import VerifiedGarbage.Impl.Bignum.Arm.InputCompare
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareArgs
import VerifiedGarbage.Proof.Bignum.Arm.SubCompare
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge

/-! ### `Bignum.Arm.CrtValidateStage`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.InputCompareLayout`, which only this module used -/

section

/-! # Range checking does not require a prevalidated modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem inputCompareLayout_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : LayoutFrameReady base len w s) :
    WP isa inputCompare s fun t => LayoutFrameReady base len w t ∧
      t.gpr .r11 = (if numAt s.mem (State.addr base) w 1 < numAt s.mem (State.addr base) w 0 then 1 else 0) ∧
      Keeps (State.addr base) len w 3 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have f0 := Nat.le_trans (array_end_le (w := w) (by decide : 0 < 8)) fits
  have f1 := Nat.le_trans (array_end_le (w := w) (by decide : 1 < 8)) fits
  have f3 := Nat.le_trans (array_end_le (w := w) (by decide : 3 < 8)) fits
  have sep1 := array_end_le (w := w) (by decide : 1 < 3)
  have sep0 := array_end_le (w := w) (by decide : 0 < 3)
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  rw [inputCompare, WP.seq_iff]
  refine WP.mono (inputCompareArgs_ok s h.workspace size header h.ptr) ?_
  rintro u ⟨p0, p10, p12, count, borrow, memU, restU⟩
  have ctx : SubCtx u base (8 * len) (arrAt w 3) (arrAt w 1) (arrAt w 0) (2 * w) :=
    ⟨h.workspace.nowrap, by omega_using [f3], by omega_using [f1], by omega_using [f0], Or.inr (by omega_using [sep1]), Or.inr (by omega_using [sep0]),
      by rw [restU.wr]; exact h.workspace.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (subCompare_ok u ctx (by omega_using [hw]) p0 p10 p12 count borrow) ?_
  rintro v ⟨value, outside, restV⟩
  rw [memU, ← numAt_native, ← numAt_native] at value
  rw [memU, show 4 * (2 * w) = 8 * w by omega_using []] at outside
  have frame := outside_workspace outside (size := 8 * len) (by omega_using [f3])
  have keeps := outside_array_keeps outside (len := len) (by have := h.workspace.nowrap; omega_using [this])
  have restUV : Rest roundClobbers s v := (restU.mono (by decide)).trans
    (restV.mono (by decide))
  refine WP.mono (restoreBase_ok v
    (by rw [restUV.rd, restUV.wr, restUV.sp]; exact h.stackRead)
    (saved_base_kept frame h.stackSep h.saved restUV.sp)) ?_
  rintro t ⟨ptr, memT, restT⟩
  rw [← memT] at frame keeps
  have rest := restUV.trans (restT.mono (by decide))
  exact ⟨h.after_array keeps frame rest ptr,
    (restT.gpr .r11 (by decide)).trans value, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtSavedSources`, which this module and modules that import it used -/

section

/-! # Instantiate private operand imports from immutable call arguments -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem CrtShared.savedOperand {g : CrtGeometry} {bs : Fin 7 → List Byte} {s : State} {child : BitVec 32}
    (h : CrtShared g bs s) (i : Fin 6)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words) :
    SavedOperand child (g.source i.succ) (workspaceWords g.words) (g.sourceLength i.succ)
      (56 + 8 * i.val) (60 + 8 * i.val) (bs i.succ) s := by
  have sub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member
  exact ⟨h.stack.nowrap, ⟨h.stack.read (by have := i.isLt; omega_using []), h.stack.read (by have := i.isLt; omega_using [])⟩, h.stack.separate.sub_right sub,
    by have := i.isLt; omega_using [], by have := i.isLt; omega_using [], h.stack.pointer i, h.stack.length i,
    h.buffers.source i.succ, (h.buffers.sourceSeparate i.succ).sub_right sub⟩

theorem CrtShared.inputSaved {g : CrtGeometry} {bs : Fin 7 → List Byte} {s : State} {child : BitVec 32}
    (h : CrtShared g bs s)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words) :
    SavedOperand child g.input (workspaceWords g.words) g.length 56 12 (bs 1) s := by
  have sub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member
  exact ⟨h.stack.nowrap, ⟨h.stack.read (by decide), h.stack.read (by decide)⟩, h.stack.separate.sub_right sub,
    by decide, by decide, h.stack.pointer 0, h.stack.count,
    h.buffers.source 1, (h.buffers.sourceSeparate 1).sub_right sub⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtLoadQStage`, which this module and modules that import it used -/

section

/-! # Import q while preserving p and the accumulated secret acceptance bit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_loadQStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.loadQ s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.loadQ, WP.seq_iff]
  refine WP.mono (crt_selectLinked_ready s h h.buffers.context.q h.q (by simp [crtRegions])
    (by have := h.buffers.context.size; omega_using [this] : 228 + 4 ≤ 8 * workspaceWords g.words)
    (by decide) ready.ptr h.main.q) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  have source : SavedOperand (crtQ g.base g.words) g.q (workspaceWords g.words) g.qLength 72 76 (bs 3) u :=
    sharedU.savedOperand 2 (by simp [crtRegions])
  rw [WP.seq_iff]
  refine WP.mono (savedOperandLayout_ok u readyU source (by decide : 0 < 8) h.buffers.qPositive
    (by have := (crt_width_valid h.buffers.lengthValid).2.2; have := h.buffers.qShort; change _ ≤ 8 * Spec.Rsa.modulusWords g.length; omega_arith)) ?_
  rintro v ⟨readyV, value, _, frameV, restV⟩
  have frameV' : Frame [⟨State.addr (crtQ g.base g.words), 8 * workspaceWords g.words⟩,
      ⟨off (State.addr u.sp) 48, 4⟩] u.mem v.mem := frameV.mono (by simp)
  have sharedV := sharedU.after_q frameV' restV ⟨readyV.layout, readyV.width⟩
  refine WP.mono (crt_selectMain_ready v sharedV) ?_
  rintro t ⟨sharedT, readyT, frameT, restT⟩
  have eqU := h.workspace_eq_after_base h.buffers.context.p (by simp [crtRegions]) frameU
  have eqV := sharedU.workspace_eq_after sharedU.buffers.context.p (by simp [crtRegions]) sharedU.buffers.context.sepPQ frameV'
  have eqT := sharedV.workspace_eq_after_base sharedV.buffers.context.p (by simp [crtRegions]) frameT
  have eqQ := sharedV.workspace_eq_after_base readyV.workspace (by simp [crtRegions]) frameT
  have prime := (eqT.number h.buffers.context.arraysFit (by decide : 0 < 8)).trans
    ((eqV.number h.buffers.context.arraysFit (by decide : 0 < 8)).trans (eqU.number h.buffers.context.arraysFit (by decide : 0 < 8)))
  have flag := (acceptance_after_base_save frameT restT).trans
    ((sharedU.acceptance_after_workspace (by simp [crtRegions]) frameV restV).trans (acceptance_after_base_save frameU restU))
  have frameVLive := crt_workspace_frame sharedU.buffers.workspace sharedU.buffers.storageFits (by simp [crtRegions]) frameV'
  rw [restU.sp] at frameVLive
  have restUV : Rest roundClobbers s v := (restU.mono (by decide)).trans restV
  rw [restUV.sp] at frameT
  exact ⟨sharedT, readyT, prime, (eqQ.number h.buffers.context.arraysFit (by decide : 0 < 8)).trans value, flag,
    (frameU.mono (by simp [crtLiveMutable])).trans (frameVLive.trans (frameT.mono (by simp [crtLiveMutable]))),
    restUV.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtLoadPStage`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CrtLoadPBody`, which this module and modules that import it used -/

section

/-! # Import p and qInv and accumulate the exact qInv < p check -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

structure CrtLoadPInput (base pp qp : BitVec 32) (len w k : Nat) (pb qb : List Byte) (s : State) : Prop where
  ready : LayoutFrameReady base len w s
  prime : SavedOperand base pp len k 64 68 pb s
  inverse : SavedOperand base qp len k 96 100 qb s
  positive : 0 < k
  fits : k ≤ 8 * w
  write : InRegions s.wr (off (State.addr s.sp) 48) 4

theorem crt_loadPBody_ok (s : State) {base pp qp : BitVec 32} {len w k : Nat} {pb qb : List Byte}
    (h : CrtLoadPInput base pp qp len w k pb qb s) :
    WP isa CrtFn.loadPBody s fun t => LayoutFrameReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = Spec.Rsa.os2ip pb ∧
      numAt t.mem (State.addr base) w 1 = Spec.Rsa.os2ip qb ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 =
        (if Spec.Rsa.os2ip qb < Spec.Rsa.os2ip pb then 1 else 0) &&& s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [CrtFn.loadPBody, WP.seq_iff]
  refine WP.mono (savedOperandLayout_ok s h.ready h.prime (by decide : 0 < 8) h.positive h.fits) ?_
  rintro u ⟨readyU, prime, _, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (savedOperandLayout_ok u readyU (h.inverse.after_workspace frameU restU)
    (by decide : 1 < 8) h.positive h.fits) ?_
  rintro v ⟨readyV, inverse, keepsV, frameV, restV⟩
  have primeV := (keeps_array_num keepsV fits op0 (by decide : 0 ≠ 1)).trans prime
  rw [WP.seq_iff]
  refine WP.mono (inputCompareLayout_ok v readyV) ?_
  rintro z ⟨readyZ, flag, keepsZ, frameZ, restZ⟩
  have primeZ := (keeps_array_num keepsZ fits op0 (by decide : 0 ≠ 3)).trans primeV
  have inverseZ := (keeps_array_num keepsZ fits op1 (by decide : 1 ≠ 3)).trans inverse
  rw [inverse, primeV] at flag
  have rest := (restU.trans restV).trans restZ
  have frame := (frameU.trans frameV).trans frameZ
  have stack := WorkspaceEq.of_frame (by decide : 112 < 2 ^ 64) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.prime.stackSeparate)
  have old : z.mem.readW (off (State.addr z.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [rest.sp]; exact stack.word (d := 48) (bits := 32) (by decide)
  refine WP.mono (mergeAcceptanceLayout_ready z readyZ
    (by rw [rest.sp]; have := h.prime.nowrap; omega_using [this]) (by rw [rest.wr, rest.sp]; exact h.write)
    (by rw [rest.sp]; exact h.prime.stackSeparate.symm.sub_right (Offset.sub_base _ (by decide)))) ?_
  rintro t ⟨readyT, saved, eq, frameT, restT, _⟩
  rw [rest.sp] at frameT
  exact ⟨readyT, (eq.number fits (by decide : 0 < 8)).trans primeZ,
    (eq.number fits (by decide : 1 < 8)).trans inverseZ, by rw [saved, flag, old],
    (frame.mono (by simp)).trans (frameT.mono (by simp)),
    rest.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm

end

end

/-! # Complete p and qInv import, validation, and return to the main workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_loadPStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.loadP s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 1 = Spec.Rsa.os2ip (bs 6) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 =
        (if Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) then 1 else 0) &&& s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.loadP, WP.seq_iff]
  refine WP.mono (crt_selectLinked_ready s h h.buffers.context.p h.p (by simp [crtRegions])
    (by have := h.buffers.context.size; omega_using [this] : 224 + 4 ≤ 8 * workspaceWords g.words)
    (by decide) ready.ptr h.main.p) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  have input : CrtLoadPInput (crtP g.base g.words) g.p g.qi (workspaceWords g.words) g.words g.pLength (bs 2) (bs 6) u :=
    ⟨readyU, sharedU.savedOperand 1 (by simp [crtRegions]), sharedU.savedOperand 5 (by simp [crtRegions]),
      h.buffers.pPositive,
      by have := (crt_width_valid h.buffers.lengthValid).2.2; have := h.buffers.pShort; change _ ≤ 8 * Spec.Rsa.modulusWords g.length; omega_arith,
      sharedU.stack.write (by decide)⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadPBody_ok u input) ?_
  rintro v ⟨readyV, prime, inverse, flag, frameV, restV⟩
  have sharedV := sharedU.after_p frameV restV ⟨readyV.layout, readyV.width⟩
  refine WP.mono (crt_selectMain_ready v sharedV) ?_
  rintro t ⟨sharedT, readyT, frameT, restT⟩
  have eq := sharedV.workspace_eq_after_base readyV.workspace (by simp [crtRegions]) frameT
  have old := acceptance_after_base_save frameU restU
  have flagT := acceptance_after_base_save frameT restT
  rw [flag, old] at flagT
  have frameV' := crt_workspace_frame sharedU.buffers.workspace sharedU.buffers.storageFits (by simp [crtRegions]) frameV
  rw [restU.sp] at frameV'
  have restUV : Rest roundClobbers s v := (restU.mono (by decide)).trans restV
  rw [restUV.sp] at frameT
  exact ⟨sharedT, readyT, (eq.number h.buffers.context.arraysFit (by decide : 0 < 8)).trans prime,
    (eq.number h.buffers.context.arraysFit (by decide : 1 < 8)).trans inverse, flagT,
    (frameU.mono (by simp [crtLiveMutable])).trans (frameV'.trans (frameT.mono (by simp [crtLiveMutable]))),
    restUV.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtAcceptStage`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CrtAcceptInput`, which this module and modules that import it used -/

section

/-! # Import the ciphertext and save its exact secret range-check bit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

structure CrtAcceptInput (base src : BitVec 32) (len w k : Nat) (bs : List Byte) (s : State) : Prop where
  ready : LayoutFrameReady base len w s
  main : CrtMainState base len w s.mem
  source : SavedOperand base src len k 56 12 bs s
  positive : 0 < k
  fits : k ≤ 8 * w
  stackFits : s.sp.toNat + 52 ≤ 2 ^ 32
  write : InRegions s.wr (off (State.addr s.sp) 48) 4
  separate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨off (State.addr s.sp) 48, 4⟩

theorem crt_acceptInput_ok (s : State) {base src : BitVec 32} {len w k : Nat} {bs : List Byte}
    (h : CrtAcceptInput base src len w k bs s) :
    WP isa CrtFn.acceptInput s fun t => LayoutFrameReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 1 = Spec.Rsa.os2ip bs ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 =
        BitVec.ofNat 32 (decide (Spec.Rsa.os2ip bs < numAt s.mem (State.addr base) w 0)).toNat ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t ∧ CrtMainState base len w t.mem := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [CrtFn.acceptInput, WP.seq_iff]
  refine WP.mono (savedOperandLayout_ok s h.ready h.source (by decide : 1 < 8) h.positive h.fits) ?_
  rintro u ⟨readyU, input, keepsU, frameU, restU⟩
  have modulus := keeps_array_num keepsU fits op0 (by decide : 0 ≠ 1)
  rw [WP.seq_iff]
  refine WP.mono (inputCompareLayout_ok u readyU) ?_
  rintro v ⟨readyV, flag, keepsV, frameV, restV⟩
  have modulusV := (keeps_array_num keepsV fits op0 (by decide : 0 ≠ 3)).trans modulus
  have inputV := (keeps_array_num keepsV fits op1 (by decide : 1 ≠ 3)).trans input
  rw [input, modulus] at flag
  have rest := restU.trans restV
  refine WP.mono (saveAcceptanceLayout_ready v readyV
    (by rw [rest.sp]; exact h.stackFits) (by rw [rest.wr, rest.sp]; exact h.write)
    (by rw [rest.sp]; exact h.separate)) ?_
  rintro t ⟨readyT, saved, eq, frameT, restT, _⟩
  rw [rest.sp] at frameT
  have size := h.main.toCrtLayoutState.size
  have header (d : Nat) (hd : d + 4 ≤ 256) :
      t.mem.readW (off (State.addr base) d) 32 = s.mem.readW (off (State.addr base) d) 32 :=
    (eq.word (d := d) (bits := 32) (by omega_using [size, hd])).trans
      ((keeps_header_readW keepsV size hd).trans (keeps_header_readW keepsU size hd))
  have mainT : CrtMainState base len w t.mem :=
    ⟨⟨readyT.layout, readyT.width⟩, (header 224 (by decide)).trans h.main.p,
      (header 228 (by decide)).trans h.main.q, (header 232 (by decide)).trans h.main.product,
      (header 236 (by decide)).trans h.main.compare, (header 240 (by decide)).trans h.main.modulus⟩
  refine ⟨readyT, (eq.number fits (by decide : 0 < 8)).trans modulusV,
    (eq.number fits (by decide : 1 < 8)).trans inputV, ?_,
    ((frameU.trans frameV).mono (by simp)).trans (frameT.mono (by simp)),
    rest.trans (restT.mono (by decide)), mainT⟩
  rw [saved, flag]
  by_cases valid : Spec.Rsa.os2ip bs < numAt s.mem (State.addr base) w 0 <;> simp [valid]

end VG.Proof.Bignum.Arm

end

end

/-! # Connect the ciphertext range check to the shared private RSA call state -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_acceptStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.acceptInput s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 =
        BitVec.ofNat 32 (decide (Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0))).toNat ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have mainSub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits
    (r := ⟨State.addr g.base, 8 * workspaceWords g.words⟩) (by simp [crtRegions])
  have input : CrtAcceptInput g.base g.input (workspaceWords g.words) g.words g.length (bs 1) s :=
    ⟨ready, h.main, h.inputSaved (by simp [crtRegions]),
      by have := h.buffers.lengthValid.1; omega_using [this], (crt_width_valid h.buffers.lengthValid).2.2,
      by have := h.stack.nowrap; omega_using [this], h.stack.write (by decide),
      (h.stack.separate.symm.sub_right (Offset.sub_base _ (by decide))).sub_left mainSub⟩
  refine WP.mono (crt_acceptInput_ok s input) ?_
  rintro t ⟨readyT, modulus, _, flag, frame, rest, mainT⟩
  rw [h.modulus] at flag
  exact ⟨h.after_main frame rest mainT modulus, readyT, flag,
    crt_workspace_frame h.buffers.workspace h.buffers.storageFits (by simp [crtRegions]) frame, rest⟩

end VG.Proof.Bignum.Arm

end

end

/-! # Exact acceptance and imported factors for the private RSA computation -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtProductStage.lean`, which only this module imported.
section

/-! # Accumulate the exact factor-product validation bit -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

/-- A number of `n` words below `2^(32 k)`, `k ≤ n`, is its first `k`. -/
theorem val32_prefix {m : Mem} {B : Addr} {d n k v : Nat} (hv : val32 m B d n = v) (hk : k ≤ n)
    (hlt : v < 2 ^ (32 * k)) : val32 m B d k = v := by
  have a := val32_append m B d k (n - k)
  rw [show k + (n - k) = n by omega, hv] at a
  have hpos := Nat.two_pow_pos (32 * k)
  rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * k) (n - k)) with h | h
  · rw [h, Nat.mul_zero, Nat.add_zero] at a; exact a.symm
  · have := Nat.le_mul_of_pos_right (2 ^ (32 * k)) h; omega

/-- The product stage, its product of `p`'s first `m` words by `q`'s first `n`
(`count`'s counts), which hold them. -/
theorem crt_productStageWith_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {count : List Instr}
    {m n : Nat} (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (hc : CountFrom count g.base g.size m n s) (hm : 0 < m) (hm' : m ≤ 2 * g.words) (hn : 0 < n)
    (hn' : n ≤ 2 * g.words)
    (fitP : numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 < 2 ^ (32 * m))
    (fitQ : numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 < 2 ^ (32 * n)) :
    WP isa (.seq (validateProductWith count) (.block mergeAcceptance)) s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 =
        (if numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 *
          numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 0) then 1 else 0) &&&
        s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_validateProductWith_ok s (h.validate_input ready) hc hm hm' hn hn') ?_
  rintro u ⟨value, outside, frame, ptr, rest⟩
  have sharedU := h.after_validation outside frame rest
  have readyU : LayoutFrameReady g.base (workspaceWords g.words) g.words u :=
    ⟨⟨sharedU.buffers.context.main, sharedU.main.layout, sharedU.main.width, ptr⟩,
      by rw [rest.rd, rest.wr, rest.sp]; exact ready.stackRead,
      by rw [rest.sp]; exact ready.stackSep,
      saved_base_kept frame (h.stack.separate.sub_left (Region.sub_prefix (by decide))) ready.saved rest.sp⟩
  have stackEq : WorkspaceEq (State.addr s.sp) 112 s.mem u.mem := WorkspaceEq.of_frame (by decide) frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stack.separate)
  have flagU : u.mem.readW (off (State.addr u.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [rest.sp]; exact stackEq.word (by decide)
  obtain ⟨pEq, qEq⟩ := h.validation_child_eq outside
  obtain ⟨pValue, qValue⟩ := h.product_values false
  rw [val32_prefix pValue hm' fitP, val32_prefix qValue hn' fitQ, h.modulus] at value
  refine WP.mono (mergeAcceptanceLayout_ready u readyU (by have := sharedU.stack.nowrap; omega)
    (sharedU.stack.write (by decide))
    ((sharedU.stack.separate.symm.sub_left (crt_region_sub_workspace sharedU.buffers.workspace sharedU.buffers.storageFits
      (by simp [crtRegions]))).sub_right (Offset.sub_base _ (by decide)))) ?_
  rintro t ⟨readyT, flagT, _, frameT, restT, _⟩
  have separate : ∀ r ∈ [⟨off (State.addr u.sp) 48, 4⟩], (⟨State.addr g.base, g.size⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact sharedU.stack.separate.symm.sub_right (Offset.sub_base _ (by decide))
  have sharedT := sharedU.after_external frameT restT (by simp [crtLiveMutable]) separate
  have eqChild (child : BitVec 32) (ws : Workspace u child (8 * workspaceWords g.words))
      (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words) :
      WorkspaceEq (State.addr child) (8 * workspaceWords g.words) u.mem t.mem :=
    WorkspaceEq.of_frame (by have := ws.nowrap; omega) frameT
      (fun r hr => (separate r hr).sub_left (crt_region_sub_workspace sharedU.buffers.workspace sharedU.buffers.storageFits member))
  rw [value, flagU] at flagT
  have frameTLive := frameT.mono (show ∀ r ∈ [⟨off (State.addr u.sp) 48, 4⟩], r ∈ crtLiveMutable g u.sp by simp [crtLiveMutable])
  rw [rest.sp] at frameTLive
  exact ⟨sharedT, readyT,
    ((eqChild _ sharedU.buffers.context.p (by simp [crtRegions])).number h.buffers.context.arraysFit (by decide)).trans
      (pEq.number h.buffers.context.arraysFit (by decide)),
    ((eqChild _ sharedU.buffers.context.q (by simp [crtRegions])).number h.buffers.context.arraysFit (by decide)).trans
      (qEq.number h.buffers.context.arraysFit (by decide)), flagT,
    (frame.mono (by simp [crtLiveMutable])).trans frameTLive,
    rest.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

def crtAccepted (bs : Fin 7 → List Byte) : Prop :=
  Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0) ∧
  Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) ∧
  Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0)
instance (bs : Fin 7 → List Byte) : Decidable (crtAccepted bs) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The checks, with the product of `p`'s first `m` words by `q`'s first `n`
(`count`'s counts), which hold them. -/
theorem crt_validateStageWith_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {count : List Instr}
    {m n : Nat} (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (hc : ∀ x, CrtShared g bs x → CountFrom count g.base g.size m n x) (hm : 0 < m) (hm' : m ≤ 2 * g.words)
    (hn : 0 < n) (hn' : n ≤ 2 * g.words) (fitP : Spec.Rsa.os2ip (bs 2) < 2 ^ (32 * m))
    (fitQ : Spec.Rsa.os2ip (bs 3) < 2 ^ (32 * n)) :
    WP isa (CrtFn.validateWith (validateProductWith count)) s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.validateWith, WP.seq_iff]
  refine WP.mono (crt_acceptStage_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, flagU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadPStage_ok u sharedU readyU) ?_
  rintro v ⟨sharedV, readyV, pV, _, flagV, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadQStage_ok v sharedV readyV) ?_
  rintro x ⟨sharedX, readyX, pX, qX, flagX, frameX, restX⟩
  refine WP.mono (crt_productStageWith_ok x sharedX readyX (hc x sharedX) hm hm' hn hn'
    (by rw [pX, pV]; exact fitP) (by rw [qX]; exact fitQ)) ?_
  rintro t ⟨sharedT, readyT, pT, qT, flagT, frameT, restT⟩
  rw [pX, pV, qX, flagX, flagV, flagU] at flagT
  have flag : t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) := by
    rw [flagT]
    by_cases hx : Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0) <;>
      by_cases hi : Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) <;>
      by_cases hp : Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0) <;>
      simp [crtAccepted, hx, hi, hp]
  rw [restU.sp] at frameV
  rw [restV.sp, restU.sp] at frameX
  rw [restX.sp, restV.sp, restU.sp] at frameT
  exact ⟨sharedT, readyT, pT.trans (pX.trans pV), qT.trans qX, flag,
    frameU.trans (frameV.trans (frameX.trans frameT)), restU.trans (restV.trans (restX.trans restT))⟩

/-- A factor of the CRT holds in the modulus's `2 W` words. -/
theorem crt_factor_fit {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s) {i : Fin 7}
    (hi : g.sourceLength i < g.length) : Spec.Rsa.os2ip (bs i) < 2 ^ (32 * (2 * g.words)) := by
  have len := (h.buffers.source i).length
  have w := (crt_width_valid h.buffers.lengthValid).2.2
  have := VG.Proof.Bignum.os2ip_lt (bs i)
  rw [len, VG.Proof.Bignum.pow256_eq] at this
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by simp only [CrtGeometry.words]; omega_using [hi, w]))

theorem crt_validateStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.validate s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have two := (crt_width_valid h.buffers.lengthValid).1
  exact crt_validateStageWith_ok s h ready (fun x hx => countFrom_productCount
      (by have := hx.buffers.storageFits
          simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, stride,
            workspaceWords] at this
          omega_using [this])
      (hx.main.toCrtLayoutState.nativeCount hx.buffers.context.main))
    (by simp only [CrtGeometry.words] at two ⊢; omega_using [two]) (Nat.le_refl _)
    (by simp only [CrtGeometry.words] at two ⊢; omega_using [two]) (Nat.le_refl _)
    (crt_factor_fit h (i := 2) h.buffers.pShort) (crt_factor_fit h (i := 3) h.buffers.qShort)

/-- The key check without `p q = n` (`CrtFn.validateGiven`), for a key whose
factors' product is the modulus. -/
theorem crt_validateGivenStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (pq : Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0))
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa (.seq CrtFn.acceptInput (.seq CrtFn.loadP CrtFn.loadQ)) s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_acceptStage_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, flagU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadPStage_ok u sharedU readyU) ?_
  rintro v ⟨sharedV, readyV, pV, _, flagV, frameV, restV⟩
  refine WP.mono (crt_loadQStage_ok v sharedV readyV) ?_
  rintro t ⟨sharedT, readyT, pT, qT, flagT, frameT, restT⟩
  rw [flagV, flagU] at flagT
  have flag : t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) := by
    rw [flagT]
    by_cases hx : Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0) <;>
      by_cases hi : Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) <;>
      simp [crtAccepted, hx, hi, pq]
  rw [restU.sp] at frameV
  rw [restV.sp, restU.sp] at frameT
  exact ⟨sharedT, readyT, pT.trans pV, qT, flag,
    frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩


end VG.Proof.Bignum.Arm

end

end

/-! # The CRT's key check and factor preparation, as parameters

The private CRT (`CrtFn.codeOf`) checks the key with `check` and prepares
each factor in the narrow workspace with `prime`: `vg_rsa_private_crt`'s
are `CrtFn.validate` and `narrowPrime`. Its proofs take any that do what
those do, for the keys `ok` holds of: `vg_rsa_private_crt_precomputed`'s
take the factors' `R² mod p` from the key's precomputed values, and need
not check `p q = n`, which those values imply. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

/-- What preparing a factor (`narrowPrime`) leaves. -/
def NarrowPrimePost (base : BitVec 32) (len v : Nat) (pb : List Byte) (s t : State) : Prop :=
  ArithmeticReady base len v t ∧
    numAt t.mem (State.addr base) v 0 =
      safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (Spec.Rsa.os2ip pb) ∧
    safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (Spec.Rsa.os2ip pb) % 2 = 1 ∧
    numAt t.mem (State.addr base) v 4 =
      2 ^ (128 * v) % safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (Spec.Rsa.os2ip pb) ∧
    t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
    Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t

/-- The factor `j.succ` (p or q), to be prepared in the narrow workspace. -/
def CrtPrimeIn (g : CrtGeometry) (bs : Fin 7 → List Byte) (j : Fin 6) (s : State) : Prop :=
  CrtShared g bs s ∧ NarrowPrimeInput (crtN g.base g.words) (g.source j.succ) (workspaceWords g.words)
    (narrowWords (g.sourceLength j.succ) g.words) (g.sourceLength j.succ) (56 + 8 * j.val) (bs j.succ) s

/-- What checking the key (`CrtFn.validate`) leaves. -/
def CrtCheckPost (g : CrtGeometry) (bs : Fin 7 → List Byte) (s t : State) : Prop :=
  CrtShared g bs t ∧ LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
    numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
    numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
    t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) ∧
    Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t

structure CrtStages where
  check : Prog isa
  prime : Nat → Prog isa
  /-- The keys the stages are for. -/
  ok : CrtGeometry → (Fin 7 → List Byte) → Prop
  checkOk : ∀ {g : CrtGeometry} {bs : Fin 7 → List Byte} (s : State), ok g bs → CrtShared g bs s →
    LayoutFrameReady g.base (workspaceWords g.words) g.words s → WP isa check s (CrtCheckPost g bs s)
  checkCt : ∀ {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte}, ok g bs1 → ok g bs2 →
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      check (fun _ _ => True)
  primeOk : ∀ {g : CrtGeometry} {bs : Fin 7 → List Byte} (j : Fin 6) (s : State), j = 1 ∨ j = 2 → ok g bs →
    CrtPrimeIn g bs j s →
    WP isa (prime (56 + 8 * j.val)) s (NarrowPrimePost (crtN g.base g.words) (workspaceWords g.words)
      (narrowWords (g.sourceLength j.succ) g.words) (bs j.succ) s)
  primeCt : ∀ {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (j : Fin 6), j = 1 ∨ j = 2 → ok g bs1 → ok g bs2 →
    RelCT isa (fun s t => CrtPrimeIn g bs1 j s ∧ CrtPrimeIn g bs2 j t ∧ s.sp = t.sp)
      (prime (56 + 8 * j.val)) (fun _ _ => True)

end VG.Proof.Bignum.Arm
