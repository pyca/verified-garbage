module

import VerifiedGarbage.Proof.Dsa.Generation.Search
import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape

/-! # Every accepted p-search result has the native arithmetic domain -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

theorem pCandidate_domain {len n q : Nat} (hw : len = 128 ∨ len = 256 ∨ len = 384)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash n bs).length = n) (seed : List Byte) (offset : Nat)
    (guard : ¬ Spec.Dsa.pCandidate (8 * len) n q seed offset < 2 ^ (8 * len - 1)) :
    PDomain len (Spec.Dsa.pCandidate (8 * len) n q seed offset) := by
  have hl : 2 ≤ 8 * len := by rcases hw with h | h | h <;> omega
  rw [pCandidate_shaped hl hlen] at guard ⊢
  have shape := VG.Proof.Ffdh.ParameterCandidate.candidate_shape hl
    (contributions n (pDigest n seed offset) ((8 * len - 1) / n + 1))
  exact pDomain_reduction hw shape.1 shape.2.2 guard

theorem primeSearch_domain {len n q value : Nat} (hw : len = 128 ∨ len = 256 ∨ len = 384)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash n bs).length = n)
    (seed : List Byte) (counters : List Nat) (rand rest : List Byte)
    (h : Spec.Dsa.primeFromSeed.search (8 * len) n q seed counters rand = some (some value, rest)) :
    PDomain len value := by
  induction counters generalizing rand with
  | nil => simp [Spec.Dsa.primeFromSeed.search] at h
  | cons c cs ih =>
    unfold Spec.Dsa.primeFromSeed.search at h
    dsimp only at h
    split at h
    · exact ih _ h
    · rename_i guard
      cases hp : Spec.Dsa.probablePrime (Spec.Dsa.pCandidate (8 * len) n q seed
        (1 + c * ((8 * len - 1) / n + 1))) rand with
      | none => simp [hp] at h
      | some pair =>
        rcases pair with ⟨accepted, remain⟩
        rw [hp] at h
        cases accepted with
        | false => exact ih remain h
        | true =>
          have hv : Spec.Dsa.pCandidate (8 * len) n q seed (1 + c * ((8 * len - 1) / n + 1)) = value := by
            simpa using congrArg (fun z => z.bind (fun p => p.1)) h
          rw [← hv]
          exact pCandidate_domain hw hlen seed _ guard

end VG.Proof.Dsa.Generation
