module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerInput
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnter
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowInput
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowExp
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowResult
import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Layout

/-! # One CRT factor's private power, computed at the factor's own width

The full-width workspace reduces the input modulo the (safe) factor; the
narrow workspace, prepared with the same safe factor at its own width,
exponentiates the reduced input; the result returns to the full-width array 6.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem powMod_mod_base (a e m : Nat) : Spec.Rsa.powMod (a % m) e m = Spec.Rsa.powMod a e m := by
  rw [powMod_eq, powMod_eq, Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod]

theorem crt_narrowPower_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (h : CrtShared g bs s) (kind : CrtChild g child slot) (j i : Fin 6)
    (pair : (j = 1 ∧ i = 3) ∨ (j = 2 ∧ i = 4))
    (input : CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words g.length
      (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) s)
    (prime : numAt s.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs j.succ)) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa ((narrowPowerWith kernel.code) slot (56 + 8 * j.val) (56 + 8 * i.val)) s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr child) g.words 0)
      CrtShared g bs t ∧ LayoutFrameReady child (workspaceWords g.words) g.words t ∧
      CrtPoweredState child (workspaceWords g.words) g.words M
        (Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs i.succ)) M) t.mem ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr s.sp, 4⟩, ⟨State.addr child, 8 * workspaceWords g.words⟩,
        ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain ⟨member, childWs, _, sepCN, slotFit, hs, _⟩ := h.child kind
  have primeJ : j = 1 ∨ j = 2 := by rcases pair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  have expI : i = 3 ∨ i = 4 := by rcases pair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  have childKind : child = crtP g.base g.words ∨ child = crtQ g.base g.words := by
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  obtain ⟨two, le, kfit, kpos, _, arrays⟩ := h.narrow_fits j primeJ
  have words := (crt_width_valid h.buffers.lengthValid).2.1
  change _ ≤ Spec.Rsa.modulusWords g.length at le
  have hi := i.isLt
  have hj := j.isLt
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have sepN : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)], (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sepCN
  let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr child) g.words 0)
  -- The input modulo the factor, at the modulus width.
  rw [narrowPowerWith, WP.seq_iff]
  refine WP.mono (crt_narrowReduce_ok s input (by change 128 * Spec.Rsa.modulusWords g.length < _; omega)) ?_
  rintro u ⟨readyU, reducedU, frameU, restU⟩
  have sharedU : CrtShared g bs u := by
    have f : Frame [⟨State.addr child, 8 * workspaceWords g.words⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem u.mem :=
      frameU.mono (by simp)
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h.after_p f restU ⟨readyU.layout, readyU.width⟩
    · exact h.after_q f restU ⟨readyU.layout, readyU.width⟩
  have flagU := h.acceptance_after_workspace member frameU restU
  -- The narrow workspace.
  rw [WP.seq_iff]
  refine WP.mono (crt_enterNarrow_ok u sharedU j primeJ) ?_
  rintro z ⟨sharedZ, selectedZ, flagZ, frameZ, restZ⟩
  have reducedZ := reducedU.congr (sharedU.eq_of_frame (childWs.congr restU.wr) member (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩])
    (frameZ.mono (by simp)) sepN)
  have flagSZ := flagZ.trans flagU
  -- The factor, prepared at the narrow width.
  have primeIn : NarrowPrimeInput (crtN g.base g.words) (g.source j.succ) (workspaceWords g.words)
      (narrowWords (g.sourceLength j.succ)) (g.sourceLength j.succ) (56 + 8 * j.val) (bs j.succ) z := by
    refine ⟨selectedZ, ?_, kpos, kfit, by have := sharedZ.stack.nowrap; omega, sharedZ.stack.read (by decide),
      by rw [flagSZ]; exact input.accepted.bit, ?_⟩
    · simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega] using sharedZ.savedOperand j sharedZ.narrow_member
    · rw [flagSZ, ← prime]; exact input.accepted.valid
  rw [WP.seq_iff]
  refine WP.mono (crt_narrowPrime_ok z primeIn (by omega)) ?_
  rintro y ⟨readyY, modY, oddY, r2Y, flagY, frameY, restY⟩
  rw [flagSZ, ← prime] at modY oddY r2Y
  have sharedY := sharedZ.after_narrow (frameY.mono (by simp)) restY
  have reducedY := reducedZ.congr (sharedZ.eq_of_frame (childWs.congr (restU.trans restZ).wr) member
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) (frameY.mono (by simp)) sepN)
  -- The reduced input, at the narrow width.
  rw [WP.seq_iff]
  refine WP.mono (crt_narrowInput_ok y sharedY readyY (sharedY.child kind).2.1 sepCN slotFit hs
    (sharedY.child kind).2.2.2.2.2.2 reducedY modY le) ?_
  rintro x ⟨readyX, inputX, keepsX, frameX, restX⟩
  have fitsN := readyY.width ▸ readyY.layout.2.2.1
  have modX := (keeps_array_num keepsX fitsN op0 (by decide)).trans modY
  have r2X := (keeps_array_num keepsX fitsN op4 (by decide)).trans r2Y
  have sharedX := sharedY.after_narrow (frameX.mono (by simp)) restX
  have reducedX := reducedY.congr (sharedY.eq_of_frame (sharedY.child kind).2.1 member
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) (frameX.mono (by simp)) sepN)
  have flagNX := sharedY.acceptance_after_workspace sharedY.narrow_member frameX restX
  -- The exponentiation.
  have expIn : NarrowExpInput (crtN g.base g.words) (g.source i.succ) (workspaceWords g.words)
      (narrowWords (g.sourceLength j.succ)) M (Spec.Rsa.os2ip (bs 1) % M) (g.sourceLength i.succ) (56 + 8 * i.val)
      (bs i.succ) x := by
    have length := h.buffers.lengthValid.2
    refine ⟨readyX, modX, oddY, inputX, r2X, by have := sharedX.stack.nowrap; omega, by omega,
      sharedX.stack.read (by omega), sharedX.stack.read (by omega), sharedX.stack.pointer i, ?_,
      sharedX.buffers.source i.succ, (sharedX.buffers.sourceSeparate i.succ).sub_right
        (crt_region_sub_workspace sharedX.buffers.workspace sharedX.buffers.storageFits sharedX.narrow_member), ?_, ?_,
        ?_⟩
    · simpa only [show 56 + 8 * i.val + 4 = 60 + 8 * i.val by omega] using sharedX.stack.length i
    · rcases expI with rfl | rfl
      · exact h.buffers.pPositive
      · exact h.buffers.qPositive
    · rcases expI with rfl | rfl
      · change g.pLength < _; have := h.buffers.pShort; omega
      · change g.qLength < _; have := h.buffers.qShort; omega
    · exact table_fits le
  rw [WP.seq_iff]
  refine WP.mono ((crt_narrowExp_ok (kernel := kernel)) x expIn) ?_
  rintro e ⟨readyE, valueE, frameE, restE⟩
  have sharedE := sharedX.after_narrow (frameE.mono (by simp)) restE
  have reducedE := reducedX.congr (sharedX.eq_of_frame (sharedX.child kind).2.1 member
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) (frameE.mono (by simp)) sepN)
  have flagNE := sharedX.acceptance_after_workspace sharedX.narrow_member frameE restE
  -- The result, back at the modulus width.
  refine WP.mono (crt_narrowResult_ok e sharedE childKind readyE valueE le slotFit hs
    (sharedE.child kind).2.2.2.2.2.2 reducedE) ?_
  rintro t ⟨sharedT, selectedT, poweredT, flagT, frameT, restT⟩
  rw [powMod_mod_base] at poweredT
  have restSU : Rest roundClobbers s u := restU
  have restSZ := restSU.trans restZ
  have restSY := restSZ.trans restY
  have restSX := restSY.trans restX
  have restSE := restSX.trans restE
  rw [restSU.sp] at frameZ
  rw [restSE.sp] at frameT
  refine ⟨sharedT, selectedT, poweredT,
    flagT.trans (flagNE.trans (flagNX.trans (flagY.trans flagSZ))),
    (frameU.mono (by simp)).trans ((frameZ.mono (by simp)).trans ((frameY.mono (by simp)).trans
      ((frameX.mono (by simp)).trans ((frameE.mono (by simp)).trans (frameT.mono (by simp)))))),
    restSE.trans restT⟩

end VG.Proof.Bignum.Arm
