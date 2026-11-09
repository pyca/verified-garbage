module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Word

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized

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

end VG.Proof.MlDsa.AArch64.Optimized
