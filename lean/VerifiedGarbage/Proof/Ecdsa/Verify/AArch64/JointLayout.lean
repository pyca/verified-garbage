import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixed
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacLayout

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Weierstrass.AArch64

namespace JointLayout

theorem layout : Weierstrass.AArch64.JointLayout P256Joint.cfg 8192 where
  lay := {
    le := by decide +kernel
    apart := by
      have h : ∀ x∈jointSlots P256Joint.cfg,∀ y∈jointSlots P256Joint.cfg,
          x≠y → x+32≤y ∨ y+32≤x := by decide +kernel
      exact fun x y hx hy hxy => h x hx y hy hxy
    mo := by decide +kernel
    tmp := by decide +kernel }
  aligned := ⟨by decide +kernel, MP'_A p256,
    fun _ _ h => nomatch (callOf_small (M := p256.MP') (by decide)).symm.trans h⟩
  n := rfl
  stableBounds := by decide +kernel
  stableSep := by decide +kernel

theorem live_slots : ∀ x∈jointLive P256Joint.cfg,x∈jointSlots P256Joint.cfg := by decide +kernel

theorem work_slots : ∀ x∈jointWork P256Joint.cfg,x∈jointSlots P256Joint.cfg := by decide +kernel

theorem generator_bits : P256Joint.cfg.gBits=1504 := rfl

theorem peer_bits : P256Joint.cfg.K.bits=1824 := rfl

theorem bits_disjoint : P256Joint.cfg.gBits+264≤P256Joint.cfg.K.bits := by decide

theorem gprep_bounds : P256Joint.cfg.gBits<4096 ∧ P256Joint.cfg.gBits%8=0 ∧ P256Joint.cfg.gBits+264≤8192 := by decide

theorem qprep_bounds : P256Joint.cfg.K.bits<4096 ∧ P256Joint.cfg.K.bits%8=0 ∧ P256Joint.cfg.K.bits+264≤8192 := by decide

theorem fixedLayout : JointFixedLayout P256Joint.cfg 8192 where
  layout := layout
  exy := rfl
  entryNodup := by decide
  accumulator := by decide
  oneLive := by decide
  oneApart := by decide
  gBits := by decide
  addApart := ⟨by decide,by decide⟩
  copyApart := ⟨by decide,by decide⟩

end JointLayout
end VG.Proof.Ecdsa.Verify.AArch64
