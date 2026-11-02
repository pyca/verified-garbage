module

public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.ModArith

/-! # A canonical Montgomery word represents an ordinary witness

This makes explicit that the shared round's universally quantified
postcondition is not vacuous: multiplication by an invertible radix
permutes all residues of the candidate. -/

@[expose] public section

namespace VG.Proof.MillerRabin

theorem round_mod (c b : Nat) :
    Proof.MillerRabin.Round.round c (b % c) = Proof.MillerRabin.Round.round c b := by
  simp only [Proof.MillerRabin.Round.round, Spec.RsaKeyGen.mrIteration,
    VG.Proof.Bignum.powMod_eq, Nat.pow_mod, Nat.mod_mod]

/-- Congruent Montgomery witnesses have the same round result. -/
theorem round_eq_of_mont {c R b b' : Nat} (hc : 0 < c) (hR : Nat.Coprime R c)
    (h : b % c * R % c = b' % c * R % c) :
    Proof.MillerRabin.Round.round c b = Proof.MillerRabin.Round.round c b' := by
  have hm := VG.Proof.RsaKeyGen.mont_inj hR (Nat.mod_lt b hc) (Nat.mod_lt b' hc) h
  rw [← round_mod c b, ← round_mod c b', hm]

theorem witness_exists {c R x : Nat} (hR : Nat.Coprime R c) (hx : x < c) :
    ∃ b, b < c ∧ x = b % c * R % c := by
  obtain ⟨b, hb, h⟩ := VG.ModArith.exists_mul_mod_eq hR (by omega) x
  exact ⟨b, hb, by rw [Nat.mod_eq_of_lt hb, h, Nat.mod_eq_of_lt hx]⟩

end VG.Proof.MillerRabin
