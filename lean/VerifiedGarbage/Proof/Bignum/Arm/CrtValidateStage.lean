module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadPStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadQStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductStage
import VerifiedGarbage.Proof.Framework.Block

/-! # Exact acceptance and imported factors for the private RSA computation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

def crtAccepted (bs : Fin 7 → List Byte) : Prop :=
  Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0) ∧
  Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) ∧
  Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0)
instance (bs : Fin 7 → List Byte) : Decidable (crtAccepted bs) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem crt_validateStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.validate s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.validate, WP.seq_iff]
  refine WP.mono (crt_acceptStage_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, flagU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadPStage_ok u sharedU readyU) ?_
  rintro v ⟨sharedV, readyV, pV, _, flagV, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadQStage_ok v sharedV readyV) ?_
  rintro x ⟨sharedX, readyX, pX, qX, flagX, frameX, restX⟩
  refine WP.mono (crt_productStage_ok x sharedX readyX) ?_
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

end VG.Proof.Bignum.Arm
