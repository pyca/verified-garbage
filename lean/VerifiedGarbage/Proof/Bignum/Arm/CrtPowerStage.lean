module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredState
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedPowerSources
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Proof.Bignum.Arm.PreparePrime
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Layout

/-! # Select a factor, compute its private power, and restore the main workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_powerStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (kind : CrtChild g child slot) (j i : Fin 6) (pair : (j = 1 ∧ i = 3) ∨ (j = 2 ∧ i = 4))
    (bit : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1)
    (valid : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≠ 0 →
      1 < numAt s.mem (State.addr child) g.words 0 ∧ numAt s.mem (State.addr child) g.words 0 % 2 = 1)
    (prime : numAt s.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs j.succ)) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa ((CrtFn.powerWith kernel.code) slot (56 + 8 * j.val) (56 + 8 * i.val)) s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr child) g.words 0)
      CrtShared g bs t ∧ LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      CrtPoweredState child (workspaceWords g.words) g.words M
        (Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs i.succ)) M) t.mem ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr child, 8 * workspaceWords g.words⟩,
        ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain ⟨member, ws, layout, _, slotFit, slotSmall, link⟩ := h.child kind
  have exponent : i = 3 ∨ i = 4 := by rcases pair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  rw [CrtFn.powerWith, WP.seq_iff]
  refine WP.mono (crt_selectLinked_ready s h ws layout member slotFit slotSmall ready.ptr link) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  have eqU := h.workspace_eq_after_base ws member frameU
  have flagU := acceptance_after_base_save frameU restU
  have modulusU := eqU.number h.buffers.context.arraysFit (by decide : 0 < 8)
  have input : CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words g.length
      (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) u :=
    ⟨⟨readyU, by have := sharedU.stack.nowrap; omega, sharedU.stack.read (by decide),
      by rw [flagU]; exact bit, by rw [flagU, modulusU]; exact valid⟩,
      sharedU.power_sources i exponent member⟩
  rw [WP.seq_iff]
  refine WP.mono ((crt_narrowPower_ok (kernel := kernel)) u sharedU kind j i pair input (by rw [modulusU]; exact prime)) ?_
  rintro v ⟨sharedV, _, powered, flagV, frameV, restV⟩
  rw [flagU, modulusU] at powered
  refine WP.mono (crt_selectMain_ready v sharedV) ?_
  rintro t ⟨sharedT, readyT, frameT, restT⟩
  have eqT := sharedV.workspace_eq_after_base (sharedV.child kind).2.1 member frameT
  have flag := (acceptance_after_base_save frameT restT).trans (flagV.trans flagU)
  have restUV : Rest roundClobbers s v := (restU.mono (by decide)).trans restV
  rw [restU.sp] at frameV
  rw [restUV.sp] at frameT
  exact ⟨sharedT, readyT, powered.congr eqT, flag,
    (frameU.mono (by simp)).trans ((frameV.mono (by simp)).trans (frameT.mono (by simp))),
    restUV.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
