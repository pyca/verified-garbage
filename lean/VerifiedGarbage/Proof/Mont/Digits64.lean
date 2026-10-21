module

public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Bignum.Words

/-! # A native paired word is a base-2⁶⁴ digit of its integer -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem word_digit64 (m : Mem) (base : Addr) (src n index : Nat) (bound : index < n) :
    (word m base (src + 8 * index)).toNat = wordsVal m base src n / 2 ^ (64 * index) % 2 ^ 64 := by
  have bridge : ∀ k, wordsVal m base src k = VG.Proof.Bignum.wv m base src k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [wordsVal_succ_top, VG.Proof.Bignum.wv, ih]
  rw [bridge]
  exact VG.Proof.Bignum.word_of_wv m base src n bound

end VG.Proof.Mont
