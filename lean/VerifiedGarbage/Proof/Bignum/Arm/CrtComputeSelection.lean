module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckedState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientSelection
public import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishSelection
public import VerifiedGarbage.Proof.Bignum.Arm.CrtResultBound
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Retain safe private arithmetic and output bounds between the computation stages -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

structure CrtPoweredPair (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  selected : CrtSelected g bs g.base s
  p : CrtPoweredState (crtP g.base g.words) (workspaceWords g.words) g.words (crtFactor bs 2)
    (Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs 4)) (crtFactor bs 2)) s.mem
  q : CrtPoweredState (crtQ g.base g.words) (workspaceWords g.words) g.words (crtFactor bs 3)
    (Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs 5)) (crtFactor bs 3)) s.mem
  flag : s.mem.readW (off (State.addr s.sp) 48) 32 = (if crtAccepted bs then 1 else 0)

theorem CrtPoweredPair.odd {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtPoweredPair g bs s) : crtFactor bs 2 % 2 = 1 := by
  by_cases accepted : crtAccepted bs
  · simpa only [crtFactor, ite_eq_left accepted] using (h.selected.1.accepted_factors accepted).1.2
  · simp [crtFactor, accepted]

theorem CrtPoweredPair.bound {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtPoweredPair g bs s) :
    Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs 4)) (crtFactor bs 2) < crtFactor bs 2 := by
  rw [powMod_eq]; exact Nat.mod_lt _ (by have := h.p.positive; omega)

theorem CrtPoweredPair.coefficientSelection {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtPoweredPair g bs s) : CrtCoefficientSelection g bs g.base s :=
  ⟨h.selected, _, _, h.p, h.odd, h.bound⟩

theorem crt_bothPowers_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtCheckedState g bs s) :
    WP isa (.seq (CrtFn.power 224 64 80) (CrtFn.power 228 72 88)) s (CrtPoweredPair g bs) :=
  (crt_bothPowers_ok s h.selected.1 h.selected.2 h.p h.q h.flag).mono
    (fun _ j => ⟨⟨j.1, j.2.1⟩, j.2.2.1, j.2.2.2.1, j.2.2.2.2.1⟩)

theorem crt_coefficientFinish_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtPoweredPair g bs s) : WP isa CrtFn.coefficientPhase s (CrtFinishSelection g bs) := by
  refine WP.mono (crt_coefficientStage_ok s h.selected.1 h.selected.2 h.p h.q h.odd h.bound) ?_
  rintro t ⟨sharedT, readyT, _, coefficient, qT, flagT, _, _⟩
  refine ⟨⟨sharedT, readyT⟩, decide (crtAccepted bs), ?_, ?_⟩
  · rw [flagT, h.flag]
    by_cases ac : crtAccepted bs <;> simp [ac]
  · intro accepted
    have ac : crtAccepted bs := of_decide_eq_true accepted
    have reconstruction : crtReconstruction g t.mem = crtPrivateValue bs := by
      unfold crtReconstruction
      rw [coefficient, qT.modulus, qT.result]
      simp only [crtFactor, ite_eq_left ac, powMod_eq, crtPrivateValue, crtResult]
      rw [Nat.mul_comm]
      exact Nat.add_comm _ _
    rw [reconstruction]
    exact h.selected.1.result_fits ac

end VG.Proof.Bignum.Arm
