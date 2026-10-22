module

public import VerifiedGarbage.Proof.Dsa.Generation.SeedResult
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix

/-! # A seed leaves a suffix of the witness tape it is given -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

theorem primeSearch_suffix {l n q : Nat} (seed : List Byte) :
    ∀ (counters : List Nat) (rand : List Byte) {p : Option Nat} {rest : List Byte},
      Spec.Dsa.primeFromSeed.search l n q seed counters rand = some (p, rest) → rest <:+ rand
  | [], rand, p, rest, h => by
    simp only [Spec.Dsa.primeFromSeed.search, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact List.suffix_refl _
  | c :: cs, rand, p, rest, h => by
    unfold Spec.Dsa.primeFromSeed.search at h
    dsimp only at h
    split at h
    · exact primeSearch_suffix seed cs rand h
    · cases hp : Spec.Dsa.probablePrime (Spec.Dsa.pCandidate l n q seed (1 + c * ((l - 1) / n + 1))) rand with
      | none => simp [hp] at h
      | some pair =>
        rcases pair with ⟨accepted, remain⟩
        rw [hp] at h
        have hs := probablePrime_suffix hp
        cases accepted with
        | false => exact (primeSearch_suffix seed cs remain h).trans hs
        | true =>
          have : remain = rest := by simpa using congrArg (fun z => z.map (·.2)) h
          exact this ▸ hs

theorem seedResult_suffix {l n : Nat} {seed : List Byte} {hs : List Nat} {rand rest : List Byte}
    {x : Option Spec.Dsa.Params} (h : seedResult l n seed hs rand = some (x, rest)) : rest <:+ rand := by
  unfold seedResult at h
  dsimp only at h
  rcases hq : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate n seed) rand with _ | ⟨_ | _, r⟩ <;> rw [hq] at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact probablePrime_suffix hq
  · have hr := probablePrime_suffix hq
    dsimp only at h
    unfold primeResult at h
    split at h
    · cases h
    · next r' hp => exact (Prod.mk.inj (Option.some.inj h)).2 ▸ (primeSearch_suffix seed _ r hp).trans hr
    · next p r' hp =>
      have hr' := (primeSearch_suffix seed _ r hp).trans hr
      unfold generatorResult at h
      split at h
      · exact (Prod.mk.inj (Option.some.inj h)).2 ▸ hr'
      · split at h <;> exact (Prod.mk.inj (Option.some.inj h)).2 ▸ hr'

end VG.Proof.Dsa.Generation
