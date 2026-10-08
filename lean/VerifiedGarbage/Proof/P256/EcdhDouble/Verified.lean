import VerifiedGarbage.Proof.P256.EcdhDouble.Field
import VerifiedGarbage.Proof.P256.Linear.Linear129
import VerifiedGarbage.Proof.P256.Linear.Linear38

/-! The selected scheduled doubling implements the original Jacobian contract. -/
namespace VG.Proof.P256.EcdhDouble.Verified
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.P256.VerifyArithmetic Spec.Weierstrass
open EcdhJac (C K M Sl live work)

theorem linear129 : LinearCorrect (Impl.P256.Linear.linear129 960 928 960) 960 928 960 12 9 := by
  intro s base hs ha hb
  exact WP.mono (Linear.linear129_ok hs (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ha hb) fun _ ⟨hr,ho,_,hv⟩ => ⟨hr,ho,hv⟩

theorem linear38 : LinearCorrect (Impl.P256.Linear.linear38 544 896 800) 544 896 800 3 8 := by
  intro s base hs ha hb
  exact WP.mono (Linear.linear38_ok hs (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ha hb) fun _ ⟨hr,ho,_,hv⟩ => ⟨hr,ho,hv⟩

theorem field_ok {base : Addr} {s : State} {E : Nat→Fe C}
    (hi : Inv M base 8192 C.p Sl live E s) :
    WP isa Impl.P256.EcdhDouble.program s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧
      Inv M base 8192 C.p Sl live (runOps (operations .doubleRR) E) t :=
  EcdhDouble.field_ok linear129 linear38 (unitMod_pow_two (by decide) _) hi

theorem double_ok (hC : Law C) (ha : AM3 C) {base : Addr} {E : Nat→Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl live E s) {P : Point C}
    (hp : onCurve C P=true) (hj : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa Impl.P256.EcdhDouble.program s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧ Inv M base 8192 C.p Sl live (runOps (operations .doubleRR) E) t ∧
      InvJ C (runOps (operations .doubleRR) E K.R.x) (runOps (operations .doubleRR) E K.R.y)
        (runOps (operations .doubleRR) E K.R.z) (add P P) :=
  EcdhDouble.double_ok linear129 linear38 (unitMod_pow_two (by decide) _) hC ha hi hp hj
end VG.Proof.P256.EcdhDouble.Verified
