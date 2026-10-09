import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.Arith.Ntt

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

/-- Integer butterfly executed by the lazy forward transform. -/
def lazyBfly (w : IPoly) (j len : Nat) (z : Int) : IPoly :=
  let t := fastMul w[j+len]! z
  (w.set! (j+len) (w[j]! - t)).set! j (w[j]! + t)

theorem toRq_get (w : IPoly) {i : Nat} (hi : i < n) :
    (toRq w)[i]! = ofInt w[i]! := by
  rw [getElem!_pos (toRq w) i hi, getElem!_pos w i hi]
  simp only [toRq, Vector.getElem_map]

theorem lazyBfly_get (w : IPoly) (j len : Nat) (z : Int) {i : Nat} (hi : i < n) :
    (lazyBfly w j len z)[i]! =
      if j = i then w[j]! + fastMul w[j+len]! z
      else if j+len = i then w[j]! - fastMul w[j+len]! z
      else w[i]! := by
  rw [getElem!_pos (lazyBfly w j len z) i hi, getElem!_pos w i hi]
  simp only [lazyBfly, Vector.getElem_set!]

theorem lazyBfly_field (w : IPoly) {j len : Nat} (hlen : 0 < len) (hj : j+len < n)
    (z : Int) : toRq (lazyBfly w j len z) = bfly (toRq w) j len (ofInt z) := by
  apply ext_getElem!
  intro i hi
  rw [toRq_get _ hi, lazyBfly_get _ _ _ _ hi, bfly_get _ hlen hj _ hi,
    toRq_get _ (by omega : j < n), toRq_get _ hj, toRq_get _ hi]
  by_cases h : i = j
  · subst i
    simp only [ite_true, ofInt_add, fastMul_field]
    rw [Fin.mul_comm]
  · by_cases h' : i = j+len
    · subst i
      simp only [Ne.symm h, h, ite_false, ite_true, ofInt_sub, fastMul_field]
      rw [Fin.mul_comm]
    · simp only [h, h', Ne.symm h, Ne.symm h', ite_false]

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
    bfly_get w hl hj z (by omega : k < n), bfly_get w hl hj z hk,
    bfly_get w hl hj z hi, bfly_get w hm hk t (by omega : j < n),
    bfly_get w hm hk t hj, bfly_get w hm hk t hi]
  simp only [h00, h01, h10, h11, Ne.symm h00, Ne.symm h01, Ne.symm h10,
    Ne.symm h11, ite_false]
  by_cases h0 : i=k <;> by_cases h1 : i=k+step <;>
    by_cases h2 : i=j <;> by_cases h3 : i=j+len <;> simp_all

/-- Pure description of a scheduled butterfly, independent of register names. -/
structure ButterflyOp where
  index : Nat
  length : Nat
  root : Int

/-- Any well-indexed scheduled sequence commutes with reduction into the field.
The separate traversal proof identifies the chosen schedule with the NTT. -/
theorem schedule_field (ops : List ButterflyOp) (w : IPoly)
    (hv : ∀ op ∈ ops, 0 < op.length ∧ op.index + op.length < n) :
    toRq (ops.foldl (fun v op => lazyBfly v op.index op.length op.root) w) =
      ops.foldl (fun v op => bfly v op.index op.length (ofInt op.root)) (toRq w) := by
  induction ops generalizing w with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun o ho => hv o (List.mem_cons_of_mem _ ho)),
      lazyBfly_field _ (hv op (by simp)).1 (hv op (by simp)).2]

end VG.Proof.MlDsa.AArch64.Optimized
