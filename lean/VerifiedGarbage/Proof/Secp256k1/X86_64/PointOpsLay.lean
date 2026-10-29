module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsFn
public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsMixed
public import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsVal

/-!
# secp256k1's point functions on x86-64: where their slots are

The slots of the functions' bodies (`fnSlots`: the temporaries, `D`, the
constants' slots of `RcbSlots`, `R`, `E` and `E`'s cached powers at byte
5408), laid out for the field arithmetic, and the facts of `FnCfg`,
`DoubleLay`, `CachedPts` and `MixedLay` about them, checked by the kernel,
with the doubling for `a = 0` (`dblJ0`).
-/

@[expose] public section

namespace VG.Proof.Secp256k1.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Secp256k1.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass.X86_64.PointOps

/-- The joint verifier's slots. -/
def K : WinCfg := publicJoint.K

/-- `E`'s cached `Z²`, then `Z³`. -/
def sel : Nat := publicJoint.selected

/-- The slots the functions' bodies use. -/
def fnSlots : List Nat := rcbW K.S K.D ++ rcbR K.S K.R K.E ++ [sel, sel + 32]

abbrev Sl : Nat → Prop := (· ∈ fnSlots)

theorem K_n : K.M.n = 4 := rfl

theorem lay : Lay K.M 8192 Sl := by
  have h : ∀ x ∈ fnSlots, ∀ y ∈ fnSlots, x ≠ y → x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    decide +kernel
  exact ⟨by decide +kernel, fun x y hx hy => h x hx y hy, by decide +kernel, by decide +kernel⟩

theorem p_odd : Spec.Weierstrass.PointOps.secp256k1.p % 2 = 1 := by decide +kernel

theorem fnCfg : FnCfg K Spec.Weierstrass.PointOps.secp256k1 Sl where
  n := rfl
  rx := rfl
  ry := rfl
  rz := rfl
  ex := rfl
  ey := rfl
  ez := rfl
  mo := rfl
  lay := lay
  modOk mem base h := by
    refine ⟨by decide, by decide, by decide, by decide, h, by decide +kernel, by decide +kernel⟩
  keep := by
    intro i hi hown hp
    simp only [Spec.Weierstrass.PointOps.Curve.Own, Spec.Weierstrass.PointOps.Curve.slot,
      Spec.Weierstrass.PointOps.Curve.tmpAt, Spec.Weierstrass.PointOps.Curve.pAt,
      Spec.Weierstrass.PointOps.Curve.ptBytes, Spec.Weierstrass.PointOps.secp256k1] at hown hp
    refine ⟨fun w hw => ?_, ?_⟩
    · have hw' : w ∈ [800, 832, 864, 896, 928, 960, 608, 640, 672, 512, 544, 576] := by
        revert w; decide +kernel
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rw [K_n]
      omega
    · have : K.M.tmp = 128 := rfl
      rw [K_n, this]
      omega
  small := by decide
  wsl w hw := by
    simp only [Sl, fnSlots]
    exact List.mem_append_left _ (by
      rcases List.mem_append.mp hw with h | h
      · exact List.mem_append_left _ h
      · revert w; decide +kernel)
  clob := by decide
  odd := p_odd

theorem doubleLay : DoubleLay K 8192 Sl dblJ0 where
  lay := lay
  apart := ⟨by decide +kernel, by decide +kernel⟩
  sl x hx := by
    simp only [Sl, fnSlots]
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · revert x; decide +kernel
  reads := by decide +kernel
  accum := by decide +kernel
  copy := by decide +kernel

theorem one_lt : K.one < Spec.Weierstrass.PointOps.secp256k1.p := by decide +kernel

theorem one_val : toM Spec.Weierstrass.PointOps.secp256k1.p (2 ^ (64 * K.M.n)) K.one = 1 := by
  have h : K.one = 1 * 2 ^ (64 * K.M.n) % Spec.Weierstrass.PointOps.secp256k1.p := by decide +kernel
  rw [h, toM_mont (unitMod_pow_two p_odd _)]
  decide +kernel

theorem cachedPts : CachedPts (m := Spec.Weierstrass.PointOps.secp256k1.p) K sel 8192 Sl dblJ0 where
  lay := {
    lay := lay
    apart := ⟨by decide +kernel, by decide +kernel⟩
    c2 := by decide +kernel
    c3 := by decide +kernel
    sl := fun x hx => by
      simp only [Sl, fnSlots]
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ h
      · revert x; decide +kernel
    head := by decide +kernel
    tail := by decide +kernel
    dbl := doubleLay.reads
    accum := doubleLay.accum
    copy := doubleLay.copy }
  dN := by decide +kernel
  eD := by decide +kernel
  rD := by decide +kernel
  one := one_lt
  oneVal := one_val

theorem mixedLay : MixedLay K 8192 Sl dblJ0 where
  lay := lay
  apart := cachedPts.lay.apart
  sl x hx := cachedPts.lay.sl x (List.mem_append_left _ hx)
  head := by decide +kernel
  tail := by decide +kernel
  dbl := doubleLay.reads
  accum := doubleLay.accum
  copy := doubleLay.copy
  dN := cachedPts.dN
  eD := cachedPts.eD

end VG.Proof.Secp256k1.X86_64.PointOps
