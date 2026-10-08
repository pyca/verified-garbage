import VerifiedGarbage.Spec.Seed

/-!
# Sixteen rounds

The code does RFC 4269 §2's round (`Spec.Seed.round`, `T = R; R = L ^ F(Ki, R);
L = T`) sixteen times, the last one included, and then takes the halves in
the other order: `crypt_eq` says that this is `crypt`, which does fifteen and
then `L = L ^ F(K16, R)` without the swap.
-/

namespace VG.Proof.Seed

open VG.Spec.Seed

abbrev Quad := Word × Word × Word × Word

/-- The first `n` rounds, with round `j + 1`'s key `key j`. -/
def roundsN (key : Nat → Word × Word) (n : Nat) (q : Quad) : Quad :=
  (List.range n).foldl (fun q j => round (key j) q) q

theorem roundsN_succ (key : Nat → Word × Word) (n : Nat) (q : Quad) :
    roundsN key (n + 1) q = round (key n) (roundsN key n q) := by
  simp [roundsN, List.range_succ, List.foldl_append]

/-- A block's words. -/
def decodeQ (b : Block) : Quad := (wordAt b 0, wordAt b 4, wordAt b 8, wordAt b 12)

/-- The block of the words `R0, R1, L0, L1` of `q = (L0, L1, R0, R1)`. -/
def encodeSwapped (q : Quad) : Block :=
  let out : Vector Word 4 := #v[q.2.2.1, q.2.2.2, q.1, q.2.1]
  Vector.ofFn fun i => (out.getD (i.val / 4) 0 >>> (8 * (3 - i.val % 4))).setWidth 8

theorem crypt_eq (key : Nat → Word × Word) (b : Block) :
    crypt key b = encodeSwapped (roundsN key 16 (decodeQ b)) := by
  rw [roundsN_succ]
  simp only [crypt, roundsN, decodeQ, encodeSwapped, round]

end VG.Proof.Seed
