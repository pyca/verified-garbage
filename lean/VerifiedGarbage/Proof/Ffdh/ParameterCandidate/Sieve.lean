module

public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Primes

/-! # FFDH parameter candidates: RSA's table gives exactly the specified sieve -/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Spec.Ffdh VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen

/-- The table omits 2, which the candidate's odd-bit check handles. -/
theorem sieve_entries : (List.range 53).map tabEntry = (VG.Spec.RsaKeyGen.smallPrimes.take 54).drop 1 := by
  rw [← primes_eq]
  unfold tabEntry slots
  rw [primes.lit_eq]
  decide +kernel

theorem sieve_cons : VG.Spec.RsaKeyGen.smallPrimes.take 54 =
    2 :: (List.range 53).map tabEntry := by
  rw [← primes_eq]
  unfold tabEntry slots
  rw [primes.lit_eq]
  decide +kernel

/-- Above the table's largest prime, its divisibility flags implement primeShape. -/
theorem primeShape_sieve {p : Nat} (hp : 8161 < p) (ho : p % 2 = 1) :
    primeShape p = !((List.range 53).any fun i => p % tabEntry i == 0) := by
  have he : ∀ s ∈ VG.Spec.RsaKeyGen.smallPrimes.take 54, (p != s) = true := by
    intro s hs
    have hb := smallPrimes_lt (List.mem_of_mem_take hs)
    simp only [bne_iff_ne]
    omega
  have ha : (VG.Spec.RsaKeyGen.smallPrimes.take 54).any (fun s => p % s == 0 && p != s) =
      (VG.Spec.RsaKeyGen.smallPrimes.take 54).any (fun s => p % s == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨s, hs, hm, _⟩
      exact ⟨s, hs, hm⟩
    · rintro ⟨s, hs, hm⟩
      exact ⟨s, hs, hm, he s hs⟩
  unfold primeShape
  rw [ha, sieve_cons]
  simp only [ show decide (p > 2) = true by simp; omega, ho, beq_self_eq_true,
    Bool.true_and, List.any_cons, List.any_map, show (1 == 0) = false from rfl, Bool.false_or]
  rfl

end VG.Proof.Ffdh.ParameterCandidate
