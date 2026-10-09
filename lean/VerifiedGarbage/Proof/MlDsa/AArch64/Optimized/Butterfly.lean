import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Word

namespace VG.Proof.MlDsa.AArch64.Optimized

/-- An ordinary forward butterfly grows the signed bound by at most 2q.
This bound covers all eight layers without canonicalizing between layers. -/
theorem butterfly_bounds {a b z bound : Int}
    (ha : -bound ≤ a ∧ a ≤ bound) (hb : -2147483648 ≤ b ∧ b < 2147483648) :
    (-bound - 16760834 < a + fastMul b z ∧ a + fastMul b z < bound + 16760834) ∧
    (-bound - 16760834 < a - fastMul b z ∧ a - fastMul b z < bound + 16760834) := by
  have hm := fastMul_bounds (z := z) hb.1 hb.2
  omega

theorem butterfly_residue (a b z : Int) :
    (a + fastMul b z) % 8380417 = (a + b * z) % 8380417 ∧
    (a - fastMul b z) % 8380417 = (a - b * z) % 8380417 := by
  have h := fastMul_mod b z
  omega

/-- Even the eighth forward layer remains signed-word safe. -/
theorem forward_bound_safe {stage : Nat} (hs : stage ≤ 8) :
    (1 + 2 * (stage : Int)) * 8380417 < 2147483648 := by omega

theorem addWord_int (a b : BitVec 32)
    (hl : -2147483648 ≤ a.toInt + b.toInt) (hh : a.toInt + b.toInt < 2147483648) :
    (a + b).toInt = a.toInt + b.toInt := by
  have he : a + b = BitVec.ofInt 32 (a.toInt + b.toInt) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  rw [he]
  exact BitVec.toInt_ofInt_eq_self (by decide) hl hh

theorem subWord_int (a b : BitVec 32)
    (hl : -2147483648 ≤ a.toInt - b.toInt) (hh : a.toInt - b.toInt < 2147483648) :
    (a - b).toInt = a.toInt - b.toInt := by
  have he : a - b = BitVec.ofInt 32 (a.toInt - b.toInt) := by
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
      BitVec.ofInt_toInt, BitVec.ofInt_toInt, BitVec.sub_eq_add_neg]
  rw [he]
  exact BitVec.toInt_ofInt_eq_self (by decide) hl hh

/-- Exact signed-lane values for a lazy forward butterfly. -/
theorem butterfly_word (a b : BitVec 32) (z : Int) {stage : Nat} (hs : stage < 8)
    (ha : -((1 + 2 * (stage : Int)) * 8380417) ≤ a.toInt ∧
      a.toInt ≤ (1 + 2 * (stage : Int)) * 8380417) :
    (a + fastMulWord b z).toInt = a.toInt + fastMul b.toInt z ∧
    (a - fastMulWord b z).toInt = a.toInt - fastMul b.toInt z := by
  have hb := butterfly_bounds (z := z) ha ⟨BitVec.le_toInt b, BitVec.toInt_lt⟩
  have hsafe := forward_bound_safe (stage := stage + 1) (by omega)
  have hm := fastMulWord_int b z
  constructor
  · rw [addWord_int a (fastMulWord b z) (by rw [hm]; omega) (by rw [hm]; omega), hm]
  · rw [subWord_int a (fastMulWord b z) (by rw [hm]; omega) (by rw [hm]; omega), hm]

end VG.Proof.MlDsa.AArch64.Optimized
