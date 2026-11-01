module

public import VerifiedGarbage.Proof.Ecdh.AArch64.CheckPoint
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Weierstrass.AArch64.P256Literals
public import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdh.AArch64.CheckPoint
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P256Literals
meta import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# `vg_p256_check_point` on AArch64: `Verified`

`check_correct` (`Proof/Ecdh/AArch64/CheckPoint.lean`) for P-256's configuration, constant
time by taint tracking (`x0` and `sp` public), and a state satisfying the contract.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P256.Check

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Ecdh.AArch64.CheckPoint
open VG.Proof.Ecdsa.AArch64

/-- P-256's curve of `Proof/Weierstrass/CheckPointContract.lean`. -/
abbrev C : Impl.Weierstrass.CheckPoint.Curve := Impl.Weierstrass.CheckPoint.p256

theorem check_curve : Impl.Ecdh.AArch64.Cfg.checkCurve p256 = some C := rfl

theorem correct (hI : Proof.Weierstrass.AArch64.InvSounds) (s : State) (hs : (ptK C).pre s) :
    ∃ t s', Exec isa (Impl.Ecdh.AArch64.Cfg.checkFn p256) s t s' ∧ abiPreserved s s' ∧ (ptK C).post s s' :=
  check_correct ((p256_ok hI).toBaseCfgOk) check_curve rfl rfl s hs

/-- Constant time by taint tracking, `x0` and `sp` public. -/
theorem ct : ConstantTime isa (ptK C).pre (ptK C).pub (Impl.Ecdh.AArch64.Cfg.checkFn p256) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) (agree C) (by taint_decide)

theorem sat : C.pre 0x1000 (satMem C) := by
  unfold Impl.Weierstrass.CheckPoint.Curve.pre
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, .inl (by decide +kernel)⟩

/-- `vg_p256_check_point` on AArch64. -/
theorem verified (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target (Impl.Ecdh.AArch64.Cfg.checkFn p256) (C.checkContract AArch64.abi) :=
  Verified.of_correct (correct hI) ct (check_implies C sat)

end VG.Proof.Ecdh.AArch64.P256.Check
