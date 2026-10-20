module

import VerifiedGarbage.Proof.Bignum.Arm.CrtBothPowers
import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishStage
public import VerifiedGarbage.Proof.Bignum.Arm.CrtResultBound
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptedFactors
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block

/-! # Private RSA computation through exact masked output -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_computeStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (p : numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2))
    (q : numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3))
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = (if crtAccepted bs then 1 else 0)) :
    WP isa CrtFn.compute s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr g.output) g.length =
        (if crtAccepted bs then Spec.Rsa.i2osp (crtPrivateValue bs) g.length else List.replicate g.length 0) ∧
      t.gpr .r0 = (if crtAccepted bs then 1 else 0) ∧
      Frame (crtLiveMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold CrtFn.compute
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (crt_bothPowers_ok s h ready p q flag) ?_
  rintro u ⟨sharedU, readyU, poweredP, poweredQ, flagU, frameU, restU⟩
  have odd : crtFactor bs 2 % 2 = 1 := by
    by_cases accepted : crtAccepted bs
    · simpa only [crtFactor, ite_eq_left accepted] using (h.accepted_factors accepted).1.2
    · simp [crtFactor, accepted]
  have bound : Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs 4)) (crtFactor bs 2) < crtFactor bs 2 := by
    rw [powMod_eq]; exact Nat.mod_lt _ (by have := poweredP.positive; omega)
  rw [WP.seq_iff]
  refine WP.mono (crt_coefficientStage_ok u sharedU readyU poweredP poweredQ odd bound) ?_
  rintro v ⟨sharedV, readyV, _, coefficient, qV, flagV, frameV, restV⟩
  have reconstruction (accepted : crtAccepted bs) : crtReconstruction g v.mem = crtPrivateValue bs := by
    unfold crtReconstruction
    rw [coefficient, qV.modulus, qV.result]
    simp only [crtFactor, ite_eq_left accepted, powMod_eq, crtPrivateValue, crtResult]
    rw [Nat.mul_comm]
    exact Nat.add_comm _ _
  have flagExport : v.mem.readW (off (State.addr v.sp) 48) 32 = BitVec.ofNat 32 (decide (crtAccepted bs)).toNat := by
    rw [flagV, flagU]
    by_cases accepted : crtAccepted bs <;> simp [accepted]
  refine WP.mono (crt_finishStage_ok v sharedV readyV flagExport (by
    intro accepted
    have ac : crtAccepted bs := of_decide_eq_true accepted
    rw [reconstruction ac]; exact h.result_fits ac)) ?_
  rintro t ⟨bytes, status, frameT, restT⟩
  have bytesT : Spec.Rsa.bytesAt t.mem (State.addr g.output) g.length =
      (if crtAccepted bs then Spec.Rsa.i2osp (crtPrivateValue bs) g.length else List.replicate g.length 0) := by
    by_cases ac : crtAccepted bs
    · simpa only [ac, decide_true, ↓reduceIte, reconstruction ac] using bytes
    · simpa only [ac, decide_false, Bool.false_eq_true, ↓reduceIte] using bytes
  have statusT : t.gpr .r0 = (if crtAccepted bs then 1 else 0) := by
    by_cases ac : crtAccepted bs <;> simpa [ac] using status
  rw [restU.sp] at frameV
  exact ⟨bytesT, statusT,
    ((frameU.trans frameV).mono (by intro r hr; exact List.mem_append_left _ hr)).trans (frameT.mono (by simp [crtLiveMutable])),
    restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
