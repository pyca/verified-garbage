import VerifiedGarbage.Proof.P384.X86_64.PointOpsVerified
import VerifiedGarbage.Proof.P384.X86_64.PointOpsLit

/-!
# P-384's point functions on x86-64: the shared contracts

The x86-64 contracts of `PointOpsVerified.lean` imply those of
`Spec.Weierstrass.PointOps.p384` (`sig_pre`, `sig_post` and `sig_pub`
evaluate them), which a working space holding `p` at slot 0 and zeros
elsewhere satisfies (`fnSat`).
-/

namespace VG.Proof.P384.X86_64.PointOps

open VG VG.X86_64 VG.Proof.Weierstrass.X86_64.PointOps
open VG.Impl.P384.X86_64.PointOps

/-! ## The shared contracts -/

/-- `p` at slot 0 of a working space at `0x1000`, the rest zeros. -/
def satMem : Mem := fun a =>
  let i := (a - 0x1000).toNat
  if 64 ≤ i ∧ i < 112 then BitVec.ofNat 8 (C.p >>> (8 * (i - 64))) else 0

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

theorem sat_p : Spec.Weierstrass.Point.p384.Below (Spec.Weierstrass.Point.p384.pointAt satMem 0x1000 C.pAt) := by
  unfold Spec.Weierstrass.Point.Curve.Below; decide +kernel

theorem sat_q : Spec.Weierstrass.Point.p384.Below (Spec.Weierstrass.Point.p384.pointAt satMem 0x1000 C.qAt) := by
  unfold Spec.Weierstrass.Point.Curve.Below; decide +kernel

theorem sat_c2 : C.CoordBelow 0x1000 satMem C.zzAt := by
  unfold Spec.Weierstrass.PointOps.Curve.CoordBelow; decide +kernel

theorem sat_c3 : C.CoordBelow 0x1000 satMem C.zzzAt := by
  unfold Spec.Weierstrass.PointOps.Curve.CoordBelow; decide +kernel

theorem sat_ret : (⟨0x8000, 8⟩ : Region).Disjoint ⟨0x1000, 8192⟩ :=
  Region.disjoint_of_le (by decide) (by decide) (by decide)

theorem doubleK_implies : doubleK.Implies (C.doubleContract X86_64.abi) where
  pre s h := by
    sig_pre [Spec.Weierstrass.PointOps.Curve.doubleContract, Spec.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2.1, h.2.2.2.2.2⟩
  post _ _ _ h := h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Weierstrass.PointOps.Curve.doubleContract, Spec.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs] at h
    exact ⟨h.1, h.2⟩
  sat := ⟨fnSat, by
    sig_pre [Spec.Weierstrass.PointOps.Curve.doubleContract, Spec.Weierstrass.PointOps.sig,
      X86_64.abi, X86_64.argRegs]
    exact ⟨sat_ret, by decide, sat_mod, sat_p⟩⟩

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
theorem double_ok : ∀ adx, wrapOk (doubleFn adx) = true
  | false => by rw [doubleLit.lit_eq]; decide +kernel
  | true => by rw [doubleAdxLit.lit_eq]; decide +kernel

theorem addCached_ok : ∀ adx, wrapOk (addCachedFn adx) = true
  | false => by rw [addCachedLit.lit_eq]; decide +kernel
  | true => by rw [addCachedAdxLit.lit_eq]; decide +kernel

theorem addAffine_ok : ∀ adx, wrapOk (addAffineFn adx) = true
  | false => by rw [addAffineLit.lit_eq]; decide +kernel
  | true => by rw [addAffineAdxLit.lit_eq]; decide +kernel

theorem double_verified (hFe : Proof.Weierstrass.Point.Fermat C.p) (adx : Bool) :
    Verified X86_64.target (doubleFn adx) (C.doubleContract X86_64.abi) :=
  Verified.of_correct (double_correct hFe adx (double_ok adx)) (double_ct adx)
    doubleK_implies

theorem addCached_verified (hFe : Proof.Weierstrass.Point.Fermat C.p) (adx : Bool) :
    Verified X86_64.target (addCachedFn adx) (C.addCachedContract X86_64.abi) :=
  Verified.of_correct (addCached_correct hFe adx (addCached_ok adx)) (addCached_ct adx)
    addCachedK_implies

theorem addAffine_verified (hFe : Proof.Weierstrass.Point.Fermat C.p) (adx : Bool) :
    Verified X86_64.target (addAffineFn adx) (C.addAffineContract X86_64.abi) :=
  Verified.of_correct (addAffine_correct hFe adx (addAffine_ok adx)) (addAffine_ct adx)
    addAffineK_implies

end VG.Proof.P384.X86_64.PointOps
