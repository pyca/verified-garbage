module

public import VerifiedGarbage.Impl.Ed25519.X86_64.Cached
public import VerifiedGarbage.Proof.Ed25519.BaseTable
public import VerifiedGarbage.Proof.Ed25519.X86_64.PointTableAddr
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Cached points

The cached addition is the specification's `pointAdd` (`grind`); each constant
field of a cached point is four immediate words stored through `rax`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off F Keeps Outside fe_st4 st4_outside)

variable {fld : Arith} [EdArith fld]

def addCachedResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * e 4
  let b := (e 1 + e 0) * e 5
  let c := e 3 * e 6
  let dd := e 2 * e 7
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAddCached_formula (e : Env) :
    point (evalOps pointAddCachedOps e) 0 1 2 3 = addCachedResult e := rfl

theorem pointAddCached_eval (e : Env) (q : Spec.Ed25519.Point) (hq : point e 4 5 6 7 = cache q) :
    point (evalOps pointAddCachedOps e) 0 1 2 3 = Spec.Ed25519.pointAdd (point e 0 1 2 3) q := by
  have h4 : e 4 = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e 5 = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e 6 = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  have h7 : e 7 = q.Z * 2 := congrArg Spec.Ed25519.Point.T hq
  rw [pointAddCached_formula]
  simp only [addCachedResult, point, Spec.Ed25519.pointAdd, h4, h5, h6, h7]
  congr 1 <;> grind

theorem pointAddCached_high (e : Env) (i : Slot) (hi : 16 ≤ i.val) :
    evalOps pointAddCachedOps e i = e i :=
  point_ops_high _ (by decide) e i hi

def addAffineResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * e 4
  let b := (e 1 + e 0) * e 5
  let c := e 3 * e 6
  let dd := e 2 + e 2
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAddAffine_formula (e : Env) :
    point (evalOps pointAddAffineOps e) 0 1 2 3 = addAffineResult e := rfl

/-- The addition of an affine cached point, `[Y - X, Y + X, 2dT]` in slots 4–6 with `2Z = 2`. -/
theorem pointAddAffine_eval (e : Env) (q : Spec.Ed25519.Point)
    (hq : (⟨e 4, e 5, e 6, 2⟩ : Spec.Ed25519.Point) = cache q) :
    point (evalOps pointAddAffineOps e) 0 1 2 3 = Spec.Ed25519.pointAdd (point e 0 1 2 3) q := by
  have h4 : e 4 = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e 5 = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e 6 = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  have h7 : (2 : Spec.X25519.Fe) = q.Z * 2 := congrArg Spec.Ed25519.Point.T hq
  have hdd : e 2 + e 2 = e 2 * (q.Z * 2) := by rw [← h7]; grind
  rw [pointAddAffine_formula]
  simp only [addAffineResult, point, Spec.Ed25519.pointAdd, h4, h5, h6, hdd]
  congr 1 <;> grind

theorem pointAddAffine_high (e : Env) (i : Slot) (hi : 16 ≤ i.val) :
    evalOps pointAddAffineOps e i = e i :=
  point_ops_high _ (by decide) e i hi

end VG.Proof.Ed25519.X86_64
