module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnter
import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowHalf
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrime
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase
public import VerifiedGarbage.Impl.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.ExpControls
public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Bignum.Arm.WindowPhaseCT
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Bignum.Arm.CallOp
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Impl.Bignum.Arm.CrtValidateProduct
import VerifiedGarbage.Impl.Bignum.Arm.MergeAcceptance
public import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationGeometry
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceLayout
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceLayout
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
import VerifiedGarbage.Impl.Bignum.Arm.SavedOperand
public import VerifiedGarbage.Impl.Bignum.Arm.InputCompare
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareArgs
import VerifiedGarbage.Proof.Bignum.Arm.SubCompare
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady

/-! ### `Bignum.Arm.CrtStages`, which this module and modules that import it used -/

section

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
    Frame [⟨State.addr base, 8 * len⟩, FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t

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

end

end

/-! ### `Bignum.Arm.CrtPowerSources`, which this module and modules that import it used -/

section

/-! # Read-only ciphertext and exponent buffers for one CRT factor -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtPowerStack.lean`, which only this module imported.
section

/-! # The immutable input and factor-exponent arguments in the CRT call frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtPowerStack (base xp ep : BitVec 32) (len k eLen slot : Nat) (s : State) : Prop where
  nowrap : s.sp.toNat + 112 ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 56) 4 ∧
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 12) 4 ∧
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) slot) 4 ∧
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) (slot + 4)) 4
  separate : Region.Disjoint ⟨State.addr s.sp, 112⟩ ⟨State.addr base, 8 * len⟩
  slotFit : slot + 8 ≤ 112
  input : s.mem.readW (off (State.addr s.sp) 56) 32 = xp
  inputCount : s.mem.readW (off (State.addr s.sp) 12) 32 = BitVec.ofNat 32 k
  exponent : s.mem.readW (off (State.addr s.sp) slot) 32 = ep
  exponentCount : s.mem.readW (off (State.addr s.sp) (slot + 4)) 32 = BitVec.ofNat 32 eLen

theorem CrtPowerStack.after_workspace {s t : State} {base xp ep : BitVec 32} {len k eLen slot : Nat} {rs : List Reg}
    (h : CrtPowerStack base xp ep len k eLen slot s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    CrtPowerStack base xp ep len k eLen slot t := by
  have eq : WorkspaceEq (State.addr s.sp) 112 s.mem t.mem := WorkspaceEq.of_frame (by decide) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate)
  have fit := h.slotFit
  refine ⟨by rw [rest.sp]; exact h.nowrap,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.readable,
    by rw [rest.sp]; exact h.separate, fit, ?_, ?_, ?_, ?_⟩
  · rw [rest.sp, eq.word (d := 56) (bits := 32) (by decide)]; exact h.input
  · rw [rest.sp, eq.word (d := 12) (bits := 32) (by decide)]; exact h.inputCount
  · rw [rest.sp, eq.word (d := slot) (bits := 32) (by omega_using [fit])]; exact h.exponent
  · rw [rest.sp, eq.word (d := slot + 4) (bits := 32) (by omega_using [fit])]; exact h.exponentCount

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

structure CrtPowerSources (base xp ep : BitVec 32) (len w k eLen slot : Nat) (xb eb : List Byte) (s : State) : Prop where
  stack : CrtPowerStack base xp ep len k eLen slot s
  input : PublicBytes xp k xb s
  exponent : PublicBytes ep eLen eb s
  inputSeparate : Region.Disjoint ⟨State.addr xp, k⟩ ⟨State.addr base, 8 * len⟩
  exponentSeparate : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr base, 8 * len⟩
  inputPositive : 0 < k
  inputFits : k ≤ 8 * w
  exponentPositive : 0 < eLen
  exponentFits : eLen < 2 ^ 32

theorem CrtPowerSources.after_workspace {s t : State} {base xp ep : BitVec 32}
    {len w k eLen slot : Nat} {xb eb : List Byte} {rs : List Reg}
    (h : CrtPowerSources base xp ep len w k eLen slot xb eb s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    CrtPowerSources base xp ep len w k eLen slot xb eb t :=
  ⟨h.stack.after_workspace frame rest,
    h.input.after_frame frame rest (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.inputSeparate),
    h.exponent.after_frame frame rest (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.exponentSeparate),
    h.inputSeparate, h.exponentSeparate, h.inputPositive, h.inputFits, h.exponentPositive, h.exponentFits⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtNarrowExp`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.WindowKernel`, which this module and modules that import it used -/

section

/-! The CRT pipeline uses one exponentiation proof for every arithmetic kernel. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

/-- The 48 bytes below the stack, for a kernel's calls, apart from the
workspace and the exponent. -/
structure KernelStack (base ep : BitVec 32) (len eLen : Nat) (s : State) : Prop where
  fit : 48 ≤ s.sp.toNat
  separate : (FrameStack.belowA s.sp 48).Disjoint ⟨State.addr base, 8 * len⟩
  exponent : (FrameStack.belowA s.sp 48).Disjoint ⟨State.addr ep, eLen⟩

/-- A windowed exponentiation, and the Montgomery product (`mul`) of the
CRT's other arithmetic. Both may write the 48 bytes below the stack, for the
calls of a shared Montgomery product (`MontCall.op`). -/
structure WindowKernel where
  code : Prog isa
  mul : CallOp
  correct : ∀ (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte},
    ExpPhaseInput base ep len w M x eb s → arrAt w 16 ≤ 8 * len →
    KernelStack base ep len eb.length s →
    WP isa code s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧
      Frame [⟨State.addr base, 8 * len⟩, FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t
  ct : ∀ {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb1 eb2 : List Byte},
    arrAt w 3 + 32 ≤ 8 * len → arrAt w 16 ≤ 8 * len → 0 < eb1.length →
    eb1.length = eb2.length →
    RelCT isa (fun s t => (ExpPhaseInput base ep len w M1 x1 eb1 s ∧ KernelStack base ep len eb1.length s) ∧
      (ExpPhaseInput base ep len w M2 x2 eb2 t ∧ KernelStack base ep len eb2.length t) ∧ s.sp = t.sp)
      code (fun _ _ => True)

def baselineWindowKernel : WindowKernel where
  code := windowExpPhase
  mul := inlineCallOp
  correct s _ _ _ _ _ _ _ h fits _ := WP.mono (windowExpPhase_ok s h fits)
    fun _ ⟨ready, value, modulus, r2, one, frame, rest⟩ =>
      ⟨ready, value, modulus, r2, one, frame.mono (by simp), rest⟩
  ct fit fits positive length := (windowExpPhase_ct fit fits positive length).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm

end

end

/-! # The private exponentiation in the narrow workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

/-- A prepared narrow workspace holding the reduced input, and the exponent's saved argument. -/
structure NarrowExpInput (base ep : BitVec 32) (len v M x eLen es : Nat) (eb : List Byte) (s : State) : Prop where
  ready : ArithmeticReady base len v s
  modulus : numAt s.mem (State.addr base) v 0 = M
  odd : M % 2 = 1
  input : numAt s.mem (State.addr base) v 1 = x
  r2 : numAt s.mem (State.addr base) v 4 = 2 ^ (128 * v) % M
  stackFit : s.sp.toNat + es + 8 ≤ 2 ^ 32
  slotSmall : es + 4 < 4096
  pointerRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) es) 4
  countRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) (es + 4)) 4
  pointer : s.mem.readW (off (State.addr s.sp) es) 32 = ep
  count : s.mem.readW (off (State.addr s.sp) (es + 4)) 32 = BitVec.ofNat 32 eLen
  exponent : PublicBytes ep eLen eb s
  separate : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr base, 8 * len⟩
  positive : 0 < eLen
  fits : eLen < 2 ^ 32
  /-- Room for the windowed exponentiation's table after the eight arrays. -/
  tableFits : arrAt v 16 ≤ 8 * len
  /-- The 48 bytes below the stack, for the kernel's calls, apart from the workspace. -/
  belowFit : 48 ≤ s.sp.toNat
  below : (FrameStack.belowA s.sp 48).Disjoint ⟨State.addr base, 8 * len⟩
  exponentBelow : (FrameStack.belowA s.sp 48).Disjoint ⟨State.addr ep, eLen⟩

/-- A narrow workspace of a width at most the modulus's has room for the table. -/
theorem table_fits {v W : Nat} (h : v ≤ W) : arrAt v 16 ≤ 8 * workspaceWords W := by
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes, workspaceWords]
  omega_using [h]

theorem crt_exponentArgs_ok (s : State) {base ep : BitVec 32} {len v M x eLen es : Nat} {eb : List Byte}
    (h : NarrowExpInput base ep len v M x eLen es eb s) :
    WP isa (.block (exponentArgs es)) s fun t =>
      t.gpr .r1 = ep ∧ t.gpr .r2 = BitVec.ofNat 32 eLen ∧ t.mem = s.mem ∧ Rest [.r1, .r2] s t := by
  have small := h.slotSmall
  unfold exponentArgs
  refine wp_loadStack (a := off (State.addr s.sp) es) (by omega_using [small])
    (addr_add (by have := h.stackFit; omega_using [this])) h.pointerRead fun u a => ?_
  refine wp_loadStack (a := off (State.addr s.sp) (es + 4)) (by omega_using [small])
    (by rw [a.sp]; exact addr_add (by have := h.stackFit; omega_using [this])) (by rw [a.rd, a.wr]; exact h.countRead)
    fun t b => WP.block_nil ?_
  exact ⟨by rw [b.other .r1 (by decide), a.gpr, h.pointer], by rw [b.gpr, a.mem, h.count],
    b.mem.trans a.mem, (a.rest (by decide)).trans (b.rest (by decide))⟩

theorem NarrowExpInput.of_mem {s t : State} {base ep : BitVec 32} {len v M x eLen es : Nat} {eb : List Byte}
    (h : NarrowExpInput base ep len v M x eLen es eb s) (mem : t.mem = s.mem) (rest : Rest [.r1, .r2] s t) :
    NarrowExpInput base ep len v M x eLen es eb t := by
  refine ⟨h.ready.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.ready.ptr), by rw [mem]; exact h.modulus, h.odd,
    by rw [mem]; exact h.input, by rw [mem]; exact h.r2, by rw [rest.sp]; exact h.stackFit, h.slotSmall,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.pointerRead, by rw [rest.rd, rest.wr, rest.sp]; exact h.countRead,
    by rw [mem, rest.sp]; exact h.pointer, by rw [mem, rest.sp]; exact h.count,
    h.exponent.after_frame (regions := []) (by rw [mem]; exact Frame.refl _ _) rest (by simp),
    h.separate, h.positive, h.fits, h.tableFits, by rw [rest.sp]; exact h.belowFit, by rw [rest.sp]; exact h.below,
    by rw [rest.sp]; exact h.exponentBelow⟩

theorem crt_narrowControls_ready (s : State) {base ep : BitVec 32} {len v M x eLen es : Nat} {eb : List Byte}
    (h : NarrowExpInput base ep len v M x eLen es eb s)
    (pointerR : s.gpr .r1 = ep) (countR : s.gpr .r2 = BitVec.ofNat 32 eLen) :
    WP isa (.block expControls) s fun t =>
      ExpPhaseInput base ep len v M x eb t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  refine WP.mono (expControls_ok s h.ready) ?_
  rintro t ⟨ready, pointer, count, arrays, frame, rest⟩
  have restT : Rest roundClobbers s t := rest.mono (by decide)
  have exponent := h.exponent.after_frame frame restT
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate)
  have positive : 0 < M := by have := h.ready.modulus; rw [h.modulus] at this; omega_using [this]
  have r2 := (arrays 4 (by decide)).trans h.r2
  refine ⟨⟨ready, (arrays 0 (by decide)).trans h.modulus, h.odd, (arrays 1 (by decide)).trans h.input,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, exponent.byte⟩, frame, restT⟩
  · rw [r2]; exact Nat.mod_lt _ positive
  · rw [r2, Nat.mod_mod, ← Nat.pow_add, show 64 * v + 64 * v = 128 * v by omega_using []]
  · rw [pointer, pointerR]
  · rw [count, countR, exponent.length]
  · rw [exponent.length]; exact h.positive
  · rw [exponent.length]; exact h.fits
  · rw [exponent.length]; exact exponent.fits
  · rw [exponent.length]; exact exponent.read
  · rw [exponent.length]; exact h.separate

theorem crt_narrowExp_ok (s : State) {base ep : BitVec 32} {len v M x eLen es : Nat} {eb : List Byte}
    (h : NarrowExpInput base ep len v M x eLen es eb s) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa ((narrowExpWith kernel.code) es) s fun t => ArithmeticReady base len v t ∧
      numAt t.mem (State.addr base) v 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M ∧
      Frame [⟨State.addr base, 8 * len⟩, FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [narrowExpWith, WP.seq_iff]
  refine WP.mono (crt_exponentArgs_ok s h) ?_
  rintro u ⟨pointerU, countU, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_narrowControls_ready u (h.of_mem memU restU) pointerU countU) ?_
  rintro z ⟨input, frameZ, restZ⟩
  obtain spZ : z.sp = s.sp := restZ.sp.trans restU.sp
  refine WP.mono (kernel.correct z input h.tableFits ⟨by rw [spZ]; exact h.belowFit, by rw [spZ]; exact h.below,
    by rw [spZ, h.exponent.length]; exact h.exponentBelow⟩) ?_
  rintro t ⟨ready, value, _, _, _, frameT, restT⟩
  rw [memU] at frameZ
  rw [spZ] at frameT
  exact ⟨ready, value, (frameZ.mono (by simp)).trans frameT, (restU.mono (by decide)).trans (restZ.trans restT)⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtPrimePowerInput`, which this module and modules that import it used -/

section

/-! # A validated factor becomes an arithmetic workspace while retaining its sources -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure CrtPrimePowerInput (base xp ep : BitVec 32) (len w k eLen slot : Nat)
    (xb eb : List Byte) (s : State) : Prop where
  accepted : AcceptedPrimeInput base len w s
  sources : CrtPowerSources base xp ep len w k eLen slot xb eb s

structure CrtPreparedPower (base xp ep : BitVec 32) (len w k eLen slot M : Nat)
    (xb eb : List Byte) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  sources : CrtPowerSources base xp ep len w k eLen slot xb eb s
  modulus : numAt s.mem (State.addr base) w 0 = M
  odd : M % 2 = 1
  r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M

theorem crt_primePower_prepare (s : State) {base xp ep : BitVec 32} {len w k eLen slot : Nat} {xb eb : List Byte}
    (h : CrtPrimePowerInput base xp ep len w k eLen slot xb eb s) (countFits : 128 * w < 2 ^ 32) :
    WP isa prepareAcceptedPrime s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr base) w 0)
      CrtPreparedPower base xp ep len w k eLen slot M xb eb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have valid := safePrime_valid h.accepted.valid
  refine WP.mono (prepareAcceptedPrime_ok s h.accepted countFits) ?_
  rintro t ⟨done, modulus, r2, frame, rest⟩
  have ready : ArithmeticReady base len w t :=
    ⟨done.workspace, done.layout, done.width, done.ptr, done.inverse,
      by rw [modulus]; exact valid.1, done.stackRead, done.stackSep, done.saved⟩
  exact ⟨⟨ready, h.sources.after_workspace frame rest, modulus, valid.2, r2⟩, frame, rest⟩

end VG.Proof.Bignum.Arm

end

end

/-! # One CRT factor's private power, computed at the factor's own width

The full-width workspace takes the input and two cleared arrays; the narrow
workspace, prepared with the safe factor at its own width, copies the factor
back to the first, reduces the input modulo it from its halves, and
exponentiates it; the result returns to the full-width array 6.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem powMod_mod_base (a e m : Nat) : Spec.Rsa.powMod (a % m) e m = Spec.Rsa.powMod a e m := by
  rw [powMod_eq, powMod_eq, Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod]

/-- The full-width factor workspace before the narrow work: the input in array 1, arrays 0 and 6 cleared. -/
structure CrtFactorMem (child : BitVec 32) (len w x : Nat) (m : Mem) : Prop where
  layout : CrtLayoutState child len w m
  input : numAt m (State.addr child) w 1 = x
  cleared0 : val32 m (State.addr child) (arrAt w 0) (2 * w + 2) = 0
  cleared6 : val32 m (State.addr child) (arrAt w 6) (2 * w + 2) = 0

theorem CrtFactorMem.congr {m m' : Mem} {child : BitVec 32} {len w x : Nat}
    (h : CrtFactorMem child len w x m) (eq : WorkspaceEq (State.addr child) (8 * len) m m') :
    CrtFactorMem child len w x m' := by
  obtain fit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  obtain fit0 := Nat.le_trans (array_end_le (w := w) (by decide : 0 < 8)) fit
  obtain fit6 := Nat.le_trans (array_end_le (w := w) (by decide : 6 < 8)) fit
  refine ⟨h.layout.congr eq, (eq.number fit (by decide)).trans h.input, ?_, ?_⟩
  · rw [← read_eq_val32, eq.read _ _ (by omega_using [fit0]), read_eq_val32]; exact h.cleared0
  · rw [← read_eq_val32, eq.read _ _ (by omega_using [fit6]), read_eq_val32]; exact h.cleared6

theorem crt_factorInput_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (h : CrtShared g bs s) (kind : CrtChild g child slot) (i : Fin 6)
    (input : CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words g.length
      (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) s) :
    WP isa factorInput s fun t =>
      CrtShared g bs t ∧ CrtFactorMem child (workspaceWords g.words) g.words (Spec.Rsa.os2ip (bs 1)) t.mem ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr child, 8 * workspaceWords g.words⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  obtain ⟨member, _, _, _, _, _, _⟩ := h.child kind
  have fits : arrAt g.words 8 ≤ 8 * workspaceWords g.words := h.buffers.context.arraysFit
  obtain op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have src := input.sources
  obtain source : SavedOperand child g.input (workspaceWords g.words) g.length 56 12 (bs 1) s :=
    ⟨src.stack.nowrap, ⟨src.stack.readable.1, src.stack.readable.2.1⟩, src.stack.separate, by decide, by decide,
      src.stack.input, src.stack.inputCount, src.input, src.inputSeparate⟩
  rw [factorInput, WP.seq_iff]
  refine WP.mono (savedOperandLayout_ok s input.accepted.toLayoutFrameReady source (by decide : 1 < 8)
    src.inputPositive src.inputFits) ?_
  rintro u ⟨readyU, valueU, _, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (clearLayout_ok u readyU (o := 0) (by decide)) ?_
  rintro z ⟨readyZ, cleared0, keepsZ, frameZ, restZ⟩
  refine WP.mono (clearLayout_ok z readyZ (o := 6) (by decide)) ?_
  rintro t ⟨readyT, cleared6, keepsT, frameT, restT⟩
  obtain frame : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩] s.mem t.mem :=
    frameU.trans (frameZ.trans frameT)
  obtain rest : Rest roundClobbers s t := restU.trans (restZ.trans restT)
  obtain layout : CrtLayoutState child (workspaceWords g.words) g.words t.mem := ⟨readyT.layout, readyT.width⟩
  obtain shared : CrtShared g bs t := by
    obtain f : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem :=
      frame.mono (by simp)
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h.after_p f rest layout
    · exact h.after_q f rest layout
  refine ⟨shared, ⟨layout, ?_, ?_, cleared6⟩, h.acceptance_after_workspace member frame rest, frame, rest⟩
  · rw [keeps_array_num keepsT fits op1 (by decide), keeps_array_num keepsZ fits op1 (by decide)]; exact valueU
  · have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
    obtain e := keeps_array_read keepsT fits op0 (by decide : (0 : Nat) ≠ 6) (d := 0)
      (n := 4 * (2 * g.words + 2)) (by omega_using [])
    simp only [Nat.add_zero] at e
    rw [← read_eq_val32, e, read_eq_val32]
    exact cleared0

theorem crt_narrowPower_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (h : CrtShared g bs s) (kind : CrtChild g child slot) (j i : Fin 6)
    (pair : (j = 1 ∧ i = 3) ∨ (j = 2 ∧ i = 4))
    (input : CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words g.length
      (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) s)
    (prime : numAt s.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs j.succ))
    (st : CrtStages) (hst : st.ok g bs) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (narrowPowerOf st.prime kernel.code slot (56 + 8 * j.val) (56 + 8 * i.val) kernel.mul.op) s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr child) g.words 0)
      CrtShared g bs t ∧
      CrtPoweredState child (workspaceWords g.words) g.words M
        (Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs i.succ)) M) t.mem ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr s.sp, 4⟩, ⟨State.addr child, 8 * workspaceWords g.words⟩,
        ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, FrameStack.belowA s.sp 48] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain ⟨member, childWs, _, sepCN, slotFit, hs, _⟩ := h.child kind
  obtain primeJ : j = 1 ∨ j = 2 := by rcases pair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  obtain expI : i = 3 ∨ i = 4 := by rcases pair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  obtain ⟨two, le, kfit, kpos, _, arrays, half⟩ := h.narrow_fits j primeJ
  obtain words : g.words ≤ 128 := (crt_width_valid h.buffers.lengthValid).2.1
  obtain wsSmall : workspaceWords g.words ≤ 16 * 128 + 64 := by simp only [workspaceWords]; omega_using [words]
  have hi := i.isLt
  have hj := j.isLt
  have fitsC : arrAt g.words 8 ≤ 8 * workspaceWords g.words := h.buffers.context.arraysFit
  obtain end0 := Nat.le_trans (array_end_le (w := g.words) (by decide : 0 < 8)) fitsC
  obtain end6 := Nat.le_trans (array_end_le (w := g.words) (by decide : 6 < 8)) fitsC
  obtain op : ∀ q, q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 6 → Operand q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain sepN : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sepCN
  obtain sepC : ∀ r ∈ [(⟨State.addr child, 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sepCN.symm
  let v := narrowWords (g.sourceLength j.succ) g.words
  let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr child) g.words 0)
  -- The input and the cleared results at the modulus width.
  rw [narrowPowerOf, WP.seq_iff]
  refine WP.mono (crt_factorInput_ok s h kind i input) ?_
  rintro u ⟨sharedU, memU, flagU, frameU, restU⟩
  -- The narrow workspace.
  rw [WP.seq_iff]
  refine WP.mono (crt_enterNarrow_ok u sharedU j primeJ) ?_
  rintro z ⟨sharedZ, selectedZ, flagZ, frameZ, restZ⟩
  obtain memZ := memU.congr (sharedU.eq_of_frame (childWs.congr restU.wr) member
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) (frameZ.mono (by simp)) sepN)
  obtain flagSZ := flagZ.trans flagU
  -- The factor, prepared at the narrow width.
  obtain primeIn : NarrowPrimeInput (crtN g.base g.words) (g.source j.succ) (workspaceWords g.words) v
      (g.sourceLength j.succ) (56 + 8 * j.val) (bs j.succ) z := by
    refine ⟨selectedZ, ?_, kpos, kfit, by have := sharedZ.stack.nowrap; omega_using [this], sharedZ.stack.read (by decide),
      by rw [flagSZ]; exact input.accepted.bit, ?_⟩
    · simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega_using []] using sharedZ.savedOperand j sharedZ.narrow_member
    · rw [flagSZ, ← prime]; exact input.accepted.valid
  rw [WP.seq_iff]
  refine WP.mono (st.primeOk j z primeJ hst ⟨sharedZ, primeIn⟩) ?_
  intro y hy
  obtain ⟨readyY, modY, oddY, r2Y, flagY, frameY, restY⟩ :
    NarrowPrimePost (crtN g.base g.words) (workspaceWords g.words) v (bs j.succ) z y := hy
  rw [flagSZ, ← prime] at modY oddY r2Y
  obtain positive : 1 < M := by have := readyY.modulus; rw [modY] at this; exact this
  obtain sharedY := sharedZ.after_narrowB (frameY.mono (by simp)) restY
  obtain memY := memZ.congr (sharedZ.eq_of_frame (sharedZ.child kind).2.1 member
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, FrameStack.belowA z.sp 48])
    (frameY.mono (by simp)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sepN _ (by simp)
      · exact sharedZ.stack.below.symm.sub_left
          (crt_region_sub_workspace sharedZ.buffers.workspace sharedZ.buffers.storageFits member)))
  have flagNY := flagY
  -- The safe factor back to the full-width array 0.
  obtain ctxY : CrtCopyCtx g bs child slot v y :=
    ⟨sharedY, readyY, (sharedY.child kind).2.1, member, (sharedY.child kind).2.2.1, sepCN, slotFit, hs,
      (sharedY.child kind).2.2.2.2.2.2, le⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_copyOut_ok y ctxY (j := 0) (a := 0) (by decide) (by decide)) ?_
  rintro x ⟨readyX, copied0, outside0, restX⟩
  obtain frameXC := outside_workspace outside0 (size := 8 * workspaceWords g.words) (by omega_using [le, end0])
  obtain keepsX := outside_array_prefix_keeps outside0 (by omega_using [wsSmall] : 8 * workspaceWords g.words < 2 ^ 64)
    (by omega_using [le] : 8 * v ≤ 8 * (g.words + 2))
  obtain layoutX : CrtLayoutState child (workspaceWords g.words) g.words x.mem := by
    obtain kl := keeps_layout memY.layout.layout (by rw [memY.layout.width]; exact keepsX)
    exact ⟨kl.2, kl.1.trans memY.layout.width⟩
  obtain sharedX : CrtShared g bs x := by
    obtain f : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr y.sp) 48, 4⟩] y.mem x.mem :=
      frameXC.mono (by simp)
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact sharedY.after_p f restX layoutX
    · exact sharedY.after_q f restX layoutX
  obtain flagNX := sharedY.acceptance_after_workspace member frameXC restX
  obtain eqNX := sharedY.eq_of_frame sharedY.buffers.context.narrow sharedY.narrow_member
    (regions := [⟨State.addr child, 8 * workspaceWords g.words⟩]) (frameXC.mono (by simp)) sepC
  obtain fitsN : arrAt v 8 ≤ 8 * workspaceWords g.words := readyY.width ▸ readyY.layout.2.2.1
  obtain modX := (eqNX.number fitsN (by decide)).trans modY
  obtain r2X := (eqNX.number fitsN (by decide)).trans r2Y
  obtain modCX : numAt x.mem (State.addr child) g.words 0 = M := by
    rw [numAt_of_copied le memY.cleared0 outside0 (by omega_using [wsSmall, end0]), copied0]
    exact modY
  obtain inputX := (keeps_array_num keepsX fitsC (op 1 (by simp)) (by decide)).trans memY.input
  obtain cleared6X : val32 x.mem (State.addr child) (arrAt g.words 6) (2 * g.words + 2) = 0 := by
    rw [outside0.val32 (Or.inr (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using [le])) (by omega_using [wsSmall, end6])]
    exact memY.cleared6
  -- The input modulo the factor.
  obtain ctxX : CrtCopyCtx g bs child slot v x :=
    ⟨sharedX, readyX, (sharedX.child kind).2.1, member, layoutX, sepCN, slotFit, hs,
      (sharedX.child kind).2.2.2.2.2.2, le⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_reduceHalf_ok x ctxX (j := 1) (by decide) half modX oddY r2X kernel.mul) ?_
  rintro e ⟨readyE, modE, r2E, _, inputE, frameE, restE⟩
  rw [inputX] at inputE
  obtain sharedE := sharedX.after_narrowB (frameE.mono (by simp)) restE
  obtain flagNE := sharedX.acceptance_after_workspaceB sharedX.narrow_member frameE restE
  obtain eqCE := sharedX.eq_of_frame (sharedX.child kind).2.1 member
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, FrameStack.belowA x.sp 48])
    (frameE.mono (by simp)) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sepN _ (by simp)
      · exact sharedX.stack.below.symm.sub_left
          (crt_region_sub_workspace sharedX.buffers.workspace sharedX.buffers.storageFits member))
  -- The exponentiation.
  obtain expIn : NarrowExpInput (crtN g.base g.words) (g.source i.succ) (workspaceWords g.words)
      v M (Spec.Rsa.os2ip (bs 1) % M) (g.sourceLength i.succ) (56 + 8 * i.val) (bs i.succ) e := by
    have length := h.buffers.lengthValid.2
    refine ⟨readyE, modE, oddY, inputE, r2E, by have := sharedE.stack.nowrap; omega_using [this], by omega_using [],
      sharedE.stack.read (by omega_using []), sharedE.stack.read (by omega_using []), sharedE.stack.pointer i, ?_,
      sharedE.buffers.source i.succ, (sharedE.buffers.sourceSeparate i.succ).sub_right
        (crt_region_sub_workspace sharedE.buffers.workspace sharedE.buffers.storageFits sharedE.narrow_member), ?_, ?_,
        ?_, sharedE.stack.belowFit, sharedE.stack.below.sub_right
          (crt_region_sub_workspace sharedE.buffers.workspace sharedE.buffers.storageFits sharedE.narrow_member),
        (sharedE.buffers.sourceBelow i.succ).symm⟩
    · simpa only [show 56 + 8 * i.val + 4 = 60 + 8 * i.val by omega_using []] using sharedE.stack.length i
    · rcases expI with rfl | rfl
      · exact h.buffers.pPositive
      · exact h.buffers.qPositive
    · rcases expI with rfl | rfl
      · change g.pLength < _; have := h.buffers.pShort; omega_using [length, this]
      · change g.qLength < _; have := h.buffers.qShort; omega_using [length, this]
    · exact table_fits le
  rw [WP.seq_iff]
  refine WP.mono ((crt_narrowExp_ok (kernel := kernel)) e expIn) ?_
  rintro r ⟨readyR, valueR, frameR, restR⟩
  rw [powMod_mod_base] at valueR
  obtain sharedR := sharedE.after_narrowB (frameR.mono (by simp)) restR
  obtain flagNR := sharedE.acceptance_after_workspaceB sharedE.narrow_member frameR restR
  obtain eqCR := sharedE.eq_of_frame (sharedE.child kind).2.1 member
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, FrameStack.belowA e.sp 48])
    (frameR.mono (by simp)) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sepN _ (by simp)
      · exact sharedE.stack.below.symm.sub_left
          (crt_region_sub_workspace sharedE.buffers.workspace sharedE.buffers.storageFits member))
  -- The result back to the full-width array 6.
  obtain layoutR := (layoutX.congr eqCE).congr eqCR
  obtain ctxR : CrtCopyCtx g bs child slot v r :=
    ⟨sharedR, readyR, (sharedR.child kind).2.1, member, layoutR, sepCN, slotFit, hs,
      (sharedR.child kind).2.2.2.2.2.2, le⟩
  refine WP.mono (crt_copyOut_ok r ctxR (j := 6) (a := 6) (by decide) (by decide)) ?_
  rintro t ⟨_, copied6, outside6, restT⟩
  obtain frameTC := outside_workspace outside6 (size := 8 * workspaceWords g.words) (by omega_using [le, end6])
  obtain keepsT := outside_array_prefix_keeps outside6 (by omega_using [wsSmall] : 8 * workspaceWords g.words < 2 ^ 64)
    (by omega_using [le] : 8 * v ≤ 8 * (g.words + 2))
  obtain layoutT : CrtLayoutState child (workspaceWords g.words) g.words t.mem := by
    obtain kl := keeps_layout layoutR.layout (by rw [layoutR.width]; exact keepsT)
    exact ⟨kl.2, kl.1.trans layoutR.width⟩
  obtain sharedT : CrtShared g bs t := by
    obtain f : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr r.sp) 48, 4⟩] r.mem t.mem :=
      frameTC.mono (by simp)
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact sharedR.after_p f restT layoutT
    · exact sharedR.after_q f restT layoutT
  obtain flagNT := sharedR.acceptance_after_workspace member frameTC restT
  obtain cleared6R : val32 r.mem (State.addr child) (arrAt g.words 6) (2 * g.words + 2) = 0 := by
    obtain f6 := Nat.le_trans (array_end_le (w := g.words) (by decide : 6 < 8)) fitsC
    rw [← read_eq_val32, eqCR.read _ _ (by omega_using [end6]), eqCE.read _ _ (by omega_using [end6]), read_eq_val32]
    exact cleared6X
  obtain modCT : numAt t.mem (State.addr child) g.words 0 = M := by
    rw [keeps_array_num keepsT fitsC (op 0 (by simp)) (by decide), eqCR.number fitsC (by decide),
      eqCE.number fitsC (by decide)]
    exact modCX
  obtain resultT : numAt t.mem (State.addr child) g.words 6 =
      Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs i.succ)) M := by
    rw [numAt_of_copied le cleared6R outside6 (by omega_using [wsSmall, end6]), copied6]
    exact valueR
  have restSU : Rest roundClobbers s u := restU
  obtain restAll : Rest roundClobbers s t :=
    restSU.trans (restZ.trans (restY.trans (restX.trans (restE.trans (restR.trans restT)))))
  refine ⟨sharedT, ⟨layoutT, positive, modCT, resultT⟩,
    flagNT.trans (flagNR.trans (flagNE.trans (flagNX.trans (flagNY.trans flagSZ)))), ?_, restAll⟩
  rw [restSU.sp] at frameZ
  rw [(restSU.trans restZ).sp] at frameY
  obtain spE : e.sp = s.sp := (restSU.trans (restZ.trans (restY.trans (restX.trans restE)))).sp
  rw [spE] at frameR
  obtain spX : x.sp = s.sp := (restSU.trans (restZ.trans (restY.trans restX))).sp
  rw [spX] at frameE
  exact (frameU.mono (by simp)).trans ((frameZ.mono (by simp)).trans ((frameY.mono (by simp)).trans
    ((frameXC.mono (by simp)).trans ((frameE.mono (by simp)).trans ((frameR.mono (by simp)).trans
      (frameTC.mono (by simp)))))))

end VG.Proof.Bignum.Arm
