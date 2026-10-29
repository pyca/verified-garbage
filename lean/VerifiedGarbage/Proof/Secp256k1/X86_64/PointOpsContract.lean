module

public import VerifiedGarbage.Proof.Secp256k1.X86_64.PointOpsVerified
import VerifiedGarbage.Proof.Secp256k1.X86_64.PointOpsLit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.Offset

/-!
# secp256k1's point functions on x86-64: the shared contracts

The x86-64 contracts of `PointOpsVerified.lean` imply those of
`Spec.Weierstrass.PointOps.secp256k1` (`sig_pre`, `sig_post` and `sig_pub`
evaluate them), which a working space holding `p` at slot 0 and zeros
elsewhere satisfies (`fnSat`).
-/

@[expose] public section

namespace VG.Proof.Secp256k1.X86_64.PointOps

open VG VG.X86_64 VG.Proof.Weierstrass.X86_64.PointOps
open VG.Impl.Secp256k1.X86_64.PointOps

/-! ## The shared contracts -/

/-- `p` at slot 0 of a working space at `0x1000`, the rest zeros. -/
def satMem : Mem := fun a =>
  let i := (a - 0x1000).toNat
  if 64 ≤ i ∧ i < 96 then BitVec.ofNat 8 (C.p >>> (8 * (i - 64))) else 0

/-- A state satisfying the preconditions. -/
def fnSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_mod : C.ModOk 0x1000 satMem := by
  unfold Spec.Weierstrass.PointOps.Curve.ModOk; decide +kernel

theorem sat_p : C.toCurve.Below (C.toCurve.pointAt satMem 0x1000 C.pAt) := by
  unfold Spec.Weierstrass.Point.Curve.Below; decide +kernel

theorem sat_q : C.toCurve.Below (C.toCurve.pointAt satMem 0x1000 C.qAt) := by
  unfold Spec.Weierstrass.Point.Curve.Below; decide +kernel

theorem sat_c2 : C.CoordBelow 0x1000 satMem C.zzAt := by
  unfold Spec.Weierstrass.PointOps.Curve.CoordBelow; decide +kernel

theorem sat_c3 : C.CoordBelow 0x1000 satMem C.zzzAt := by
  unfold Spec.Weierstrass.PointOps.Curve.CoordBelow; decide +kernel

theorem sat_ret : (⟨0x8000, 8⟩ : Region).Disjoint ⟨0x1000, 8192⟩ :=
  Region.disjoint_of_le (by decide) (by decide) (by decide)

theorem addCachedK_implies : addCachedK.Implies (C.addCachedContract X86_64.abi) where
  pre s h := by
    sig_pre [Spec.Weierstrass.PointOps.Curve.addCachedContract, Spec.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩
  post _ _ _ h := h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Weierstrass.PointOps.Curve.addCachedContract, Spec.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩
  sat := ⟨fnSat, by
    sig_pre [Spec.Weierstrass.PointOps.Curve.addCachedContract, Spec.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs]
    exact ⟨sat_ret, by decide, sat_mod, sat_p, sat_q, sat_c2, sat_c3⟩⟩

theorem addAffineK_implies : addAffineK.Implies (C.addAffineContract X86_64.abi) where
  pre s h := by
    sig_pre [Spec.Weierstrass.PointOps.Curve.addAffineContract, Spec.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  post _ _ _ h := h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Weierstrass.PointOps.Curve.addAffineContract, Spec.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩
  sat := ⟨fnSat, by
    sig_pre [Spec.Weierstrass.PointOps.Curve.addAffineContract, Spec.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs]
    exact ⟨sat_ret, by decide, sat_mod, sat_p, sat_q⟩⟩

/-! ## `Verified` -/

/-- The functions' code passes `wrapOk` (checked on the literals). -/
theorem addCached_ok : wrapOk addCachedFn = true := by
  rw [addCachedLit.lit_eq]; decide +kernel

theorem addAffine_ok : wrapOk addAffineFn = true := by
  rw [addAffineLit.lit_eq]; decide +kernel

theorem addCached_verified (hFe : Proof.Weierstrass.Point.Fermat C.p) :
    Verified X86_64.target addCachedFn (C.addCachedContract X86_64.abi) :=
  Verified.of_correct (addCached_correct hFe addCached_ok) addCached_ct addCachedK_implies

theorem addAffine_verified (hFe : Proof.Weierstrass.Point.Fermat C.p) :
    Verified X86_64.target addAffineFn (C.addAffineContract X86_64.abi) :=
  Verified.of_correct (addAffine_correct hFe addAffine_ok) addAffine_ct addAffineK_implies

end VG.Proof.Secp256k1.X86_64.PointOps
