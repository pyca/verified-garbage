module

public import VerifiedGarbage.Spec.MillerRabin
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin

/-! # A canonical Montgomery word represents an ordinary witness

This makes explicit that the shared round's universally quantified
postcondition is not vacuous: multiplication by an invertible radix
permutes all residues of the candidate. -/

@[expose] public section

namespace VG.Proof.MillerRabin

theorem round_mod (c b : Nat) :
    Spec.MillerRabin.round c (b % c) = Spec.MillerRabin.round c b := by
  simp only [Spec.MillerRabin.round, Spec.RsaKeyGen.mrIteration,
    VG.Proof.Bignum.powMod_eq, Nat.pow_mod, Nat.mod_mod]

/-- Congruent Montgomery witnesses have the same round result. -/
theorem round_eq_of_mont {c R b b' : Nat} (hc : 0 < c) (hR : Nat.Coprime R c)
    (h : b % c * R % c = b' % c * R % c) :
    Spec.MillerRabin.round c b = Spec.MillerRabin.round c b' := by
  have hm := VG.Proof.RsaKeyGen.mont_inj hR (Nat.mod_lt b hc) (Nat.mod_lt b' hc) h
  rw [← round_mod c b, ← round_mod c b', hm]

theorem witness_exists {c R x : Nat} (hR : Nat.Coprime R c) (hx : x < c) :
    ∃ b, b < c ∧ x = b % c * R % c := by
  let f : Fin c → Fin c := fun b => ⟨b.val * R % c, Nat.mod_lt _ (by omega)⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Fin.ext
    exact VG.Proof.RsaKeyGen.mont_inj hR a.isLt b.isLt (congrArg Fin.val h)
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective hf ⟨x, hx⟩
  exact ⟨b.val, b.isLt, by
    have h := congrArg Fin.val hb
    simpa only [f, Nat.mod_eq_of_lt b.isLt] using h.symm⟩

end VG.Proof.MillerRabin
