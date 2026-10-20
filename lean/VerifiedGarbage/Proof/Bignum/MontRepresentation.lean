module

import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Data.Fintype.EquivFin

/-! # Every reduced residue has a Montgomery representation -/

@[expose] public section
namespace VG.Proof.Bignum

theorem mont_representation {R m v : Nat} (coprime : Nat.Coprime R m) (bound : v < m) :
    ∃ x : Nat, v = x * R % m := by
  let f : Fin m → Fin m := fun x => ⟨x.val * R % m, Nat.mod_lt _ (by omega)⟩
  have injective : Function.Injective f := by
    intro x y equal
    have E : x.val * R % m = y.val * R % m := congrArg Fin.val equal
    have V := mont_cancel coprime E
    rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at V
    exact Fin.ext V
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective injective ⟨v, bound⟩
  exact ⟨x.val, (congrArg Fin.val hx).symm⟩

end VG.Proof.Bignum
