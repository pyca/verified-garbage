import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttSpec

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Integer inverse butterfly, retaining the lazy sum and reducing its difference. -/
def lazyInverseBfly (w : IPoly) (j len : Nat) (z : Int) : IPoly :=
  (w.set! (j+len) (fastMul (w[j]! - w[j+len]!) z)).set! j (w[j]!+w[j+len]!)

theorem lazyInverseBfly_get (w : IPoly) (j len : Nat) (z : Int) {i : Nat} (hi : i < n) :
    (lazyInverseBfly w j len z)[i]! =
      if j = i then w[j]! + w[j+len]!
      else if j+len = i then fastMul (w[j]! - w[j+len]!) z
      else w[i]! := by
  rw [getElem!_pos (lazyInverseBfly w j len z) i hi, getElem!_pos w i hi]
  simp only [lazyInverseBfly, Vector.getElem_set!]

theorem lazyInverseBfly_field (w : IPoly) {j len : Nat} (hlen : 0 < len) (hj : j+len < n)
    (z : Int) : toRq (lazyInverseBfly w j len z) = bflyInv (toRq w) j len (ofInt z) := by
  apply ext_getElem!
  intro i hi
  rw [toRq_get _ hi, lazyInverseBfly_get _ _ _ _ hi, bflyInv_get _ hlen hj _ hi,
    toRq_get _ (by omega : j < n), toRq_get _ hj, toRq_get _ hi]
  by_cases h : i = j
  · subst i
    simp only [ite_true, ofInt_add]
  · by_cases h' : i = j+len
    · subst i
      simp only [Ne.symm h, h, ite_false, ite_true, fastMul_field, ofInt_sub]
      rw [Fin.mul_comm]
    · simp only [h, h', Ne.symm h, Ne.symm h', ite_false]


namespace InverseTraversal

def valid (o : Op) : Bool := decide (0<o.length ∧ o.index+o.length<n)

theorem local_valid : localSchedule.all valid=true := by decide +kernel
theorem strided_valid : stridedSchedule.all valid=true := by decide +kernel

def Op.applyInt (o : Op) (w : IPoly) : IPoly :=
  lazyInverseBfly w o.index o.length (negZetaNat o.rootIndex : Int)

def runInt (ops : List Op) (w : IPoly) : IPoly := ops.foldl (fun w o => o.applyInt w) w

theorem ofInt_negZetaNat (k : Nat) : ofInt (negZetaNat k : Int) = -zetas k := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [VG.Proof.MlDsa.KeyGen.ofInt_val]
  rw [Int.emod_eq_of_lt (by omega) (by have := negZetaNat_lt k; change _<8380417 at this; omega)]
  exact congrArg (fun n : Nat => (n : Int)) (negZetaNat_eq k)

theorem applyInt_field (o : Op) (w : IPoly) (h : valid o=true) :
    toRq (o.applyInt w)=o.apply (toRq w) := by
  have hv : 0<o.length ∧ o.index+o.length<n := of_decide_eq_true h
  rw [Op.applyInt,lazyInverseBfly_field _ hv.1 hv.2,ofInt_negZetaNat]
  rfl

theorem runInt_field (ops : List Op) (w : IPoly) (hv : ops.all valid=true) :
    toRq (runInt ops w)=run ops (toRq w) := by
  induction ops generalizing w with
  | nil => rfl
  | cons o ops ih =>
    have hs : valid o=true ∧ ops.all valid=true := by
      simpa only [List.all_cons,Bool.and_eq_true] using hv
    simp only [runInt,run,List.foldl_cons] at ⊢
    rw [← runInt,ih _ hs.2,applyInt_field _ _ hs.1]
    rfl

/-- Exact modular result for the integer schedule with the selected compensated scale. -/
theorem traversal_field (w : IPoly) :
    (toRq (runInt stridedSchedule (runInt localSchedule w))).map (· * 16382)=
      montgomeryNttInv (toRq w) := by
  rw [runInt_field _ _ strided_valid,runInt_field _ _ local_valid,traversal_montgomery]

end InverseTraversal

end VG.Proof.MlDsa.AArch64.Optimized
