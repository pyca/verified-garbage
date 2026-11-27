module

public import VerifiedGarbage.Proof.MlDsa.Arith.Schedule
public import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Arithmetic
import Std.Data.DTreeMap.Internal.Operations

/-! ### `MlDsa.AArch64.Optimized.NttSpec`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

/-- Butterflies acting on disjoint coefficient pairs commute. This is the
only reordering needed to fuse independent outer and inner NTT slices. -/
theorem bfly_comm (w : Poly) {j len k step : Nat} (hl : 0 < len) (hm : 0 < step)
    (hj : j + len < n) (hk : k + step < n)
    (h00 : j ≠ k) (h01 : j ≠ k + step) (h10 : j + len ≠ k) (h11 : j + len ≠ k + step)
    (z t : Zq) :
    bfly (bfly w j len z) k step t = bfly (bfly w k step t) j len z := by
  apply ext_getElem!
  intro i hi
  rw [bfly_get (bfly w j len z) hm hk t hi, bfly_get (bfly w k step t) hl hj z hi,
    bfly_get w hl hj z (by omega_using [hk] : k < n), bfly_get w hl hj z hk,
    bfly_get w hl hj z hi, bfly_get w hm hk t (by omega_using [hj] : j < n),
    bfly_get w hm hk t hj, bfly_get w hm hk t hi]
  simp only [h00, h01, h10, h11, Ne.symm h00, Ne.symm h01, Ne.symm h10,
    Ne.symm h11, ite_false]
  by_cases h0 : i=k <;> by_cases h1 : i=k+step <;>
    by_cases h2 : i=j <;> by_cases h3 : i=j+len <;> simp_all

end VG.Proof.MlDsa.AArch64.Optimized

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- A butterfly with its root-table index retained symbolically. -/
structure Op where
  index : Nat
  length : Nat
  rootIndex : Nat
  deriving DecidableEq, Repr

def Op.apply (o : Op) (w : Poly) : Poly := bfly w o.index o.length (zetas o.rootIndex)
def run (ops : List Op) (w : Poly) : Poly := ops.foldl (fun w o => o.apply w) w

def outerSlice (u : Nat) : List Op :=
  ([4,2,1] : List Nat).flatMap fun gap =>
    (List.range (4/gap)).flatMap fun g =>
      (List.range gap).flatMap fun j =>
        (List.range 4).map fun e =>
          ⟨64*gap*g+32*j+4*u+e,32*gap,4/gap+g⟩

def innerSlice (u : Nat) : List Op :=
  (([4,2,1] : List Nat).flatMap fun gap =>
    (List.range (4/gap)).flatMap fun g =>
      (List.range gap).flatMap fun j =>
        (List.range 4).map fun e =>
          ⟨32*u+8*gap*g+4*j+e,4*gap,32/gap+(4/gap)*u+g⟩) ++
  ((List.range 4).flatMap fun group =>
    ([2,1] : List Nat).flatMap fun len =>
      (List.range (4/len)).flatMap fun g =>
        (List.range len).map fun j =>
          ⟨32*u+8*group+2*len*g+j,len,128/len+16*u/len+4*group/len+g⟩)

def outerSchedule : List Op := (List.range 8).flatMap outerSlice
def innerSchedule : List Op := (List.range 8).flatMap innerSlice

def layerSchedule (len : Nat) : List Op :=
  (List.range (128/len)).flatMap fun g =>
    (List.range len).map fun j => ⟨2*len*g+j,len,128/len+g⟩

def standardOuter : List Op := ([128,64,32] : List Nat).flatMap layerSchedule
def standardInner : List Op := ([16,8,4,2,1] : List Nat).flatMap layerSchedule

/-- The coefficients a butterfly touches (`Schedule.bflyMask`). -/
def mask (o : Op) : Nat := Schedule.bflyMask o.index o.length

/-- Butterflies with disjoint masks commute. -/
theorem mask_comm {a b : Op} (h : (mask a &&& mask b) = 0) (w : Poly) :
    b.apply (a.apply w) = a.apply (b.apply w) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := Schedule.bflyMask_disjoint h
  exact bfly_comm w h0 h2 h1 h3 h4 h5 h6 h7 _ _

/-- The place of a butterfly in the standard order. -/
def key (o : Op) : Nat := (256-o.length)*256+o.index

end VG.Proof.MlDsa.AArch64.Optimized.Traversal
