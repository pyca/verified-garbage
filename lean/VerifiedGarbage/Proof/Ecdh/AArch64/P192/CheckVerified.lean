module

public import VerifiedGarbage.Proof.Ecdh.AArch64.CheckPoint
meta import VerifiedGarbage.Proof.Ecdh.AArch64.CheckPoint
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P192Literals
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P192Literals
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# `vg_p192_check_point` on AArch64: `Verified`

`check_correct` (`Proof/Ecdh/AArch64/CheckPoint.lean`) for P-192's configuration, constant
time by taint tracking (`x0` and `sp` public), and a state satisfying the contract.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P192.Check

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Ecdh.AArch64.CheckPoint
open VG.Proof.Ecdsa.AArch64.P192

/-- P-192's curve of `Spec/Weierstrass/CheckPoint.lean`. -/
abbrev C : Spec.Weierstrass.CheckPoint.Curve := Spec.Weierstrass.CheckPoint.p192

theorem check_curve : Impl.Ecdh.AArch64.Cfg.checkCurve p192 = some C := rfl

theorem correct (hI : Proof.Weierstrass.AArch64.InvSounds) (s : State) (hs : (ptK C).pre s) :
    ∃ t s', Exec isa (Impl.Ecdh.AArch64.Cfg.checkFn p192) s t s' ∧ abiPreserved s s' ∧ (ptK C).post s s' :=
  check_correct (p192_ok hI) check_curve rfl rfl s hs

/-- Constant time by taint tracking, `x0` and `sp` public. -/
theorem ct : ConstantTime isa (ptK C).pre (ptK C).pub (Impl.Ecdh.AArch64.Cfg.checkFn p192) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) (agree C) (by taint_decide)

theorem sat : C.pre 0x1000 (satMem C) := by
  unfold Spec.Weierstrass.CheckPoint.Curve.pre
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, .inl (by decide +kernel)⟩

/-- `vg_p192_check_point` on AArch64. -/
theorem verified (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target (Impl.Ecdh.AArch64.Cfg.checkFn p192) (C.checkContract AArch64.abi) :=
  Verified.of_correct (correct hI) ct (check_implies C sat)

end VG.Proof.Ecdh.AArch64.P192.Check
