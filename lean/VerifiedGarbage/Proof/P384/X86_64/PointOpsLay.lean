import VerifiedGarbage.Impl.P384.X86_64.PointOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsFn
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsCT

/-!
# P-384's point functions on x86-64: where their slots are

The slots of the functions' bodies (`fnSlots`: the temporaries, `D`, the
constants' slots of `RcbSlots`, `R`, `E` and `E`'s cached powers at byte
6160), laid out for the field arithmetic, and the facts of `FnCfg`,
`DoubleLay`, `CachedPts` and `MixedLay` about them, checked by the kernel.
-/

namespace VG.Proof.P384.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.P384.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass.X86_64.PointOps

/-- The joint verifier's slots, with the products of the baseline or BMI2 and ADX. -/
def K (adx : Bool) : WinCfg := if adx then publicJointAdx.K else publicJoint.K

/-- `E`'s cached `Z²`, then `Z³`. -/
def sel : Nat := publicJoint.selected

/-- The slots the functions' bodies use. -/
def fnSlots (adx : Bool) : List Nat :=
  rcbW (K adx).S (K adx).D ++ rcbR (K adx).S (K adx).R (K adx).E ++ [sel, sel + 48]

abbrev Sl (adx : Bool) : Nat → Prop := (· ∈ fnSlots adx)

theorem K_n (adx : Bool) : (K adx).M.n = 6 := by cases adx <;> rfl

theorem lay (adx : Bool) : Lay (K adx).M 8192 (Sl adx) := by
  have h : ∀ x ∈ fnSlots adx, ∀ y ∈ fnSlots adx, x ≠ y → x + 8 * (K adx).M.n ≤ y ∨ y + 8 * (K adx).M.n ≤ x := by
    cases adx <;> decide +kernel
  exact ⟨by cases adx <;> decide +kernel, fun x y hx hy => h x hx y hy, by cases adx <;> decide +kernel,
    by cases adx <;> decide +kernel⟩

theorem p_odd : Spec.Weierstrass.PointOps.p384.p % 2 = 1 := by decide +kernel

theorem fnCfg (adx : Bool) : FnCfg (K adx) Spec.Weierstrass.PointOps.p384 (Sl adx) where
  n := by cases adx <;> rfl
  rx := by cases adx <;> rfl
  ry := by cases adx <;> rfl
  rz := by cases adx <;> rfl
  ex := by cases adx <;> rfl
  ey := by cases adx <;> rfl
  ez := by cases adx <;> rfl
  mo := by cases adx <;> rfl
  lay := lay adx
  modOk mem base h := by
    refine ⟨by cases adx <;> decide, by cases adx <;> decide, by cases adx <;> decide,
      by cases adx <;> decide, h, by cases adx <;> decide +kernel, by cases adx <;> decide +kernel⟩
  keep := by
    intro i hi hown hp
    simp only [Spec.Weierstrass.PointOps.Curve.Own, Spec.Weierstrass.PointOps.Curve.slot,
      Spec.Weierstrass.PointOps.Curve.tmpAt, Spec.Weierstrass.PointOps.Curve.pAt,
      Spec.Weierstrass.PointOps.Curve.ptBytes, Spec.Weierstrass.PointOps.p384,
      Spec.Weierstrass.Point.p384] at hown hp
    refine ⟨fun w hw => ?_, ?_⟩
    · have hw' : w ∈ [1168, 1216, 1264, 1312, 1360, 1408, 880, 928, 976, 736, 784, 832] := by
        cases adx <;> revert w <;> decide +kernel
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rw [K_n]
      omega
    · have : (K adx).M.tmp = 4048 := by cases adx <;> rfl
      rw [K_n, this]
      omega
  small := by decide
  wsl w hw := by
    simp only [Sl, fnSlots]
    exact List.mem_append_left _ (by
      rcases List.mem_append.mp hw with h | h
      · exact List.mem_append_left _ h
      · cases adx <;> revert w <;> decide +kernel)
  clob := by cases adx <;> decide
  odd := p_odd

theorem doubleLay (adx : Bool) : DoubleLay (K adx) 8192 (Sl adx) where
  lay := lay adx
  apart := by cases adx <;> exact ⟨by decide +kernel, by decide +kernel⟩
  sl x hx := by
    simp only [Sl, fnSlots]
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · cases adx <;> revert x <;> decide +kernel
  reads := by cases adx <;> decide +kernel
  accum := by cases adx <;> decide +kernel
  copy := by cases adx <;> decide +kernel

theorem one_lt (adx : Bool) : (K adx).one < Spec.Weierstrass.PointOps.p384.p := by
  cases adx <;> decide +kernel

theorem one_val (adx : Bool) :
    toM Spec.Weierstrass.PointOps.p384.p (2 ^ (64 * (K adx).M.n)) (K adx).one = 1 := by
  have h : (K adx).one = 1 * 2 ^ (64 * (K adx).M.n) % Spec.Weierstrass.PointOps.p384.p := by
    cases adx <;> decide +kernel
  rw [h, toM_mont (unitMod_pow_two p_odd _)]
  decide +kernel

theorem cachedPts (adx : Bool) : CachedPts (m := Spec.Weierstrass.PointOps.p384.p) (K adx) sel 8192 (Sl adx) where
  lay := {
    lay := lay adx
    apart := by cases adx <;> exact ⟨by decide +kernel, by decide +kernel⟩
    c2 := by cases adx <;> decide +kernel
    c3 := by cases adx <;> decide +kernel
    sl := fun x hx => by
      simp only [Sl, fnSlots]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ h
      · cases adx <;> revert x <;> decide +kernel
    head := by cases adx <;> decide +kernel
    tail := by cases adx <;> decide +kernel
    dbl := (doubleLay adx).reads
    accum := (doubleLay adx).accum
    copy := (doubleLay adx).copy }
  dN := by cases adx <;> decide +kernel
  eD := by cases adx <;> decide +kernel
  rD := by cases adx <;> decide +kernel
  one := one_lt adx
  oneVal := one_val adx

theorem mixedLay (adx : Bool) : MixedLay (K adx) 8192 (Sl adx) where
  lay := lay adx
  apart := (cachedPts adx).lay.apart
  sl x hx := (cachedPts adx).lay.sl x (List.mem_append_left _ hx)
  head := by cases adx <;> decide +kernel
  tail := by cases adx <;> decide +kernel
  dbl := (doubleLay adx).reads
  accum := (doubleLay adx).accum
  copy := (doubleLay adx).copy
  dN := (cachedPts adx).dN
  eD := (cachedPts adx).eD

end VG.Proof.P384.X86_64.PointOps
