import VerifiedGarbage.Proof.Framework.Pratt
import Mathlib.Data.ZMod.Basic

/-!
# Pratt certificates: `powMod` in `ZMod`

`powMod m n b e` is `b ^ e` in `ZMod m` (`powMod_cast`), for the proofs that
compute a power in a field `ZMod p` with it (Ed448's and X448's square
roots). It is apart from `Pratt.lean`, whose importers need no `ZMod`.
-/

namespace VG.Proof.Pratt

theorem powMod_cast (m : Nat) (n b e : Nat) (he : e < 2 ^ n) :
    (powMod m n b e : ZMod m) = (b : ZMod m) ^ e := by
  induction n generalizing b e with
  | zero =>
    have : e = 0 := by simpa using he
    subst this; simp [powMod]
  | succ n ih =>
    by_cases h0 : e = 0
    · subst h0; simp [powMod]
    have he2 : e / 2 < 2 ^ n := by rw [Nat.pow_succ] at he; omega
    have hb : ((b * b % m : Nat) : ZMod m) = (b : ZMod m) ^ 2 := by
      rw [ZMod.natCast_mod, Nat.cast_mul, sq]
    have hsplit : (b : ZMod m) ^ e = ((b : ZMod m) ^ 2) ^ (e / 2) * (b : ZMod m) ^ (e % 2) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    by_cases h2 : e % 2 = 0
    · simp only [powMod, h0, h2, ite_false, ite_true]
      rw [ih _ _ he2, hb, hsplit, h2, pow_zero, mul_one]
    · simp only [powMod, h0, h2, ite_false]
      have h1 : e % 2 = 1 := by omega
      rw [ZMod.natCast_mod, Nat.cast_mul, ih _ _ he2, hb, hsplit, h1, pow_one, mul_comm]

end VG.Proof.Pratt
