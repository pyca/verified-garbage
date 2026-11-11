module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerInput
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnter
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStages
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopy
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowHalf
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowExp
import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
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
  have fit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  have fit0 := Nat.le_trans (array_end_le (w := w) (by decide : 0 < 8)) fit
  have fit6 := Nat.le_trans (array_end_le (w := w) (by decide : 6 < 8)) fit
  refine ⟨h.layout.congr eq, (eq.number fit (by decide)).trans h.input, ?_, ?_⟩
  · rw [← read_eq_val32, eq.read _ _ (by omega), read_eq_val32]; exact h.cleared0
  · rw [← read_eq_val32, eq.read _ _ (by omega), read_eq_val32]; exact h.cleared6

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
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have src := input.sources
  have source : SavedOperand child g.input (workspaceWords g.words) g.length 56 12 (bs 1) s :=
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
  have frame : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩] s.mem t.mem :=
    frameU.trans (frameZ.trans frameT)
  have rest : Rest roundClobbers s t := restU.trans (restZ.trans restT)
  have layout : CrtLayoutState child (workspaceWords g.words) g.words t.mem := ⟨readyT.layout, readyT.width⟩
  have shared : CrtShared g bs t := by
    have f : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem :=
      frame.mono (by simp)
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h.after_p f rest layout
    · exact h.after_q f rest layout
  refine ⟨shared, ⟨layout, ?_, ?_, cleared6⟩, h.acceptance_after_workspace member frame rest, frame, rest⟩
  · rw [keeps_array_num keepsT fits op1 (by decide), keeps_array_num keepsZ fits op1 (by decide)]; exact valueU
  · have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
    have e := keeps_array_read keepsT fits op0 (by decide : (0 : Nat) ≠ 6) (d := 0)
      (n := 4 * (2 * g.words + 2)) (by omega)
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
    WP isa ((narrowPowerOf st.prime kernel.code) slot (56 + 8 * j.val) (56 + 8 * i.val)) s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr child) g.words 0)
      CrtShared g bs t ∧
      CrtPoweredState child (workspaceWords g.words) g.words M
        (Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs i.succ)) M) t.mem ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr s.sp, 4⟩, ⟨State.addr child, 8 * workspaceWords g.words⟩,
        ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain ⟨member, childWs, _, sepCN, slotFit, hs, _⟩ := h.child kind
  have primeJ : j = 1 ∨ j = 2 := by rcases pair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  have expI : i = 3 ∨ i = 4 := by rcases pair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  obtain ⟨two, le, kfit, kpos, _, arrays, half⟩ := h.narrow_fits j primeJ
  have words : g.words ≤ 128 := (crt_width_valid h.buffers.lengthValid).2.1
  have wsSmall : workspaceWords g.words ≤ 16 * 128 + 64 := by simp only [workspaceWords]; omega
  have hi := i.isLt
  have hj := j.isLt
  have fitsC : arrAt g.words 8 ≤ 8 * workspaceWords g.words := h.buffers.context.arraysFit
  have end0 := Nat.le_trans (array_end_le (w := g.words) (by decide : 0 < 8)) fitsC
  have end6 := Nat.le_trans (array_end_le (w := g.words) (by decide : 6 < 8)) fitsC
  have op : ∀ q, q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 6 → Operand q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have sepN : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sepCN
  have sepC : ∀ r ∈ [(⟨State.addr child, 8 * workspaceWords g.words⟩ : Region)],
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
  have memZ := memU.congr (sharedU.eq_of_frame (childWs.congr restU.wr) member
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) (frameZ.mono (by simp)) sepN)
  have flagSZ := flagZ.trans flagU
  -- The factor, prepared at the narrow width.
  have primeIn : NarrowPrimeInput (crtN g.base g.words) (g.source j.succ) (workspaceWords g.words) v
      (g.sourceLength j.succ) (56 + 8 * j.val) (bs j.succ) z := by
    refine ⟨selectedZ, ?_, kpos, kfit, by have := sharedZ.stack.nowrap; omega, sharedZ.stack.read (by decide),
      by rw [flagSZ]; exact input.accepted.bit, ?_⟩
    · simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega] using sharedZ.savedOperand j sharedZ.narrow_member
    · rw [flagSZ, ← prime]; exact input.accepted.valid
  rw [WP.seq_iff]
  refine WP.mono (st.primeOk j z primeJ hst ⟨sharedZ, primeIn⟩) ?_
  intro y hy
  obtain ⟨readyY, modY, oddY, r2Y, flagY, frameY, restY⟩ :
    NarrowPrimePost (crtN g.base g.words) (workspaceWords g.words) v (bs j.succ) z y := hy
  rw [flagSZ, ← prime] at modY oddY r2Y
  have positive : 1 < M := by have := readyY.modulus; rw [modY] at this; exact this
  have sharedY := sharedZ.after_narrow (frameY.mono (by simp)) restY
  have memY := memZ.congr (sharedZ.eq_of_frame (sharedZ.child kind).2.1 member
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) (frameY.mono (by simp)) sepN)
  have flagNY := flagY
  -- The safe factor back to the full-width array 0.
  have ctxY : CrtCopyCtx g bs child slot v y :=
    ⟨sharedY, readyY, (sharedY.child kind).2.1, member, (sharedY.child kind).2.2.1, sepCN, slotFit, hs,
      (sharedY.child kind).2.2.2.2.2.2, le⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_copyOut_ok y ctxY (j := 0) (a := 0) (by decide) (by decide)) ?_
  rintro x ⟨readyX, copied0, outside0, restX⟩
  have frameXC := outside_workspace outside0 (size := 8 * workspaceWords g.words) (by omega)
  have keepsX := outside_array_prefix_keeps outside0 (by omega : 8 * workspaceWords g.words < 2 ^ 64)
    (by omega : 8 * v ≤ 8 * (g.words + 2))
  have layoutX : CrtLayoutState child (workspaceWords g.words) g.words x.mem := by
    have kl := keeps_layout memY.layout.layout (by rw [memY.layout.width]; exact keepsX)
    exact ⟨kl.2, kl.1.trans memY.layout.width⟩
  have sharedX : CrtShared g bs x := by
    have f : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr y.sp) 48, 4⟩] y.mem x.mem :=
      frameXC.mono (by simp)
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact sharedY.after_p f restX layoutX
    · exact sharedY.after_q f restX layoutX
  have flagNX := sharedY.acceptance_after_workspace member frameXC restX
  have eqNX := sharedY.eq_of_frame sharedY.buffers.context.narrow sharedY.narrow_member
    (regions := [⟨State.addr child, 8 * workspaceWords g.words⟩]) (frameXC.mono (by simp)) sepC
  have fitsN : arrAt v 8 ≤ 8 * workspaceWords g.words := readyY.width ▸ readyY.layout.2.2.1
  have modX := (eqNX.number fitsN (by decide)).trans modY
  have r2X := (eqNX.number fitsN (by decide)).trans r2Y
  have modCX : numAt x.mem (State.addr child) g.words 0 = M := by
    rw [numAt_of_copied le memY.cleared0 outside0 (by omega), copied0]
    exact modY
  have inputX := (keeps_array_num keepsX fitsC (op 1 (by simp)) (by decide)).trans memY.input
  have cleared6X : val32 x.mem (State.addr child) (arrAt g.words 6) (2 * g.words + 2) = 0 := by
    rw [outside0.val32 (Or.inr (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega)) (by omega)]
    exact memY.cleared6
  -- The input modulo the factor.
  have ctxX : CrtCopyCtx g bs child slot v x :=
    ⟨sharedX, readyX, (sharedX.child kind).2.1, member, layoutX, sepCN, slotFit, hs,
      (sharedX.child kind).2.2.2.2.2.2, le⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_reduceHalf_ok x ctxX (j := 1) (by decide) half modX oddY r2X) ?_
  rintro e ⟨readyE, modE, r2E, _, inputE, frameE, restE⟩
  rw [inputX] at inputE
  have sharedE := sharedX.after_narrow (frameE.mono (by simp)) restE
  have flagNE := sharedX.acceptance_after_workspace sharedX.narrow_member frameE restE
  have eqCE := sharedX.eq_of_frame (sharedX.child kind).2.1 member
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) (frameE.mono (by simp)) sepN
  -- The exponentiation.
  have expIn : NarrowExpInput (crtN g.base g.words) (g.source i.succ) (workspaceWords g.words)
      v M (Spec.Rsa.os2ip (bs 1) % M) (g.sourceLength i.succ) (56 + 8 * i.val) (bs i.succ) e := by
    have length := h.buffers.lengthValid.2
    refine ⟨readyE, modE, oddY, inputE, r2E, by have := sharedE.stack.nowrap; omega, by omega,
      sharedE.stack.read (by omega), sharedE.stack.read (by omega), sharedE.stack.pointer i, ?_,
      sharedE.buffers.source i.succ, (sharedE.buffers.sourceSeparate i.succ).sub_right
        (crt_region_sub_workspace sharedE.buffers.workspace sharedE.buffers.storageFits sharedE.narrow_member), ?_, ?_,
        ?_⟩
    · simpa only [show 56 + 8 * i.val + 4 = 60 + 8 * i.val by omega] using sharedE.stack.length i
    · rcases expI with rfl | rfl
      · exact h.buffers.pPositive
      · exact h.buffers.qPositive
    · rcases expI with rfl | rfl
      · change g.pLength < _; have := h.buffers.pShort; omega
      · change g.qLength < _; have := h.buffers.qShort; omega
    · exact table_fits le
  rw [WP.seq_iff]
  refine WP.mono ((crt_narrowExp_ok (kernel := kernel)) e expIn) ?_
  rintro r ⟨readyR, valueR, frameR, restR⟩
  rw [powMod_mod_base] at valueR
  have sharedR := sharedE.after_narrow (frameR.mono (by simp)) restR
  have flagNR := sharedE.acceptance_after_workspace sharedE.narrow_member frameR restR
  have eqCR := sharedE.eq_of_frame (sharedE.child kind).2.1 member
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) (frameR.mono (by simp)) sepN
  -- The result back to the full-width array 6.
  have layoutR := (layoutX.congr eqCE).congr eqCR
  have ctxR : CrtCopyCtx g bs child slot v r :=
    ⟨sharedR, readyR, (sharedR.child kind).2.1, member, layoutR, sepCN, slotFit, hs,
      (sharedR.child kind).2.2.2.2.2.2, le⟩
  refine WP.mono (crt_copyOut_ok r ctxR (j := 6) (a := 6) (by decide) (by decide)) ?_
  rintro t ⟨_, copied6, outside6, restT⟩
  have frameTC := outside_workspace outside6 (size := 8 * workspaceWords g.words) (by omega)
  have keepsT := outside_array_prefix_keeps outside6 (by omega : 8 * workspaceWords g.words < 2 ^ 64)
    (by omega : 8 * v ≤ 8 * (g.words + 2))
  have layoutT : CrtLayoutState child (workspaceWords g.words) g.words t.mem := by
    have kl := keeps_layout layoutR.layout (by rw [layoutR.width]; exact keepsT)
    exact ⟨kl.2, kl.1.trans layoutR.width⟩
  have sharedT : CrtShared g bs t := by
    have f : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr r.sp) 48, 4⟩] r.mem t.mem :=
      frameTC.mono (by simp)
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact sharedR.after_p f restT layoutT
    · exact sharedR.after_q f restT layoutT
  have flagNT := sharedR.acceptance_after_workspace member frameTC restT
  have cleared6R : val32 r.mem (State.addr child) (arrAt g.words 6) (2 * g.words + 2) = 0 := by
    have f6 := Nat.le_trans (array_end_le (w := g.words) (by decide : 6 < 8)) fitsC
    rw [← read_eq_val32, eqCR.read _ _ (by omega), eqCE.read _ _ (by omega), read_eq_val32]
    exact cleared6X
  have modCT : numAt t.mem (State.addr child) g.words 0 = M := by
    rw [keeps_array_num keepsT fitsC (op 0 (by simp)) (by decide), eqCR.number fitsC (by decide),
      eqCE.number fitsC (by decide)]
    exact modCX
  have resultT : numAt t.mem (State.addr child) g.words 6 =
      Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs i.succ)) M := by
    rw [numAt_of_copied le cleared6R outside6 (by omega), copied6]
    exact valueR
  have restSU : Rest roundClobbers s u := restU
  have restAll : Rest roundClobbers s t :=
    restSU.trans (restZ.trans (restY.trans (restX.trans (restE.trans (restR.trans restT)))))
  refine ⟨sharedT, ⟨layoutT, positive, modCT, resultT⟩,
    flagNT.trans (flagNR.trans (flagNE.trans (flagNX.trans (flagNY.trans flagSZ)))), ?_, restAll⟩
  rw [restSU.sp] at frameZ
  exact (frameU.mono (by simp)).trans ((frameZ.mono (by simp)).trans ((frameY.mono (by simp)).trans
    ((frameXC.mono (by simp)).trans ((frameE.mono (by simp)).trans ((frameR.mono (by simp)).trans
      (frameTC.mono (by simp)))))))

end VG.Proof.Bignum.Arm
