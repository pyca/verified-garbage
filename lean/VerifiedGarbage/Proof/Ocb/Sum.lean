import VerifiedGarbage.Proof.Ocb.Spec

/-!
# OCB: the sum of `HASH` a chunk at a time

Untrusted: everything here is checked by Lean. `Sum_{j+c}` is `Sum_j` with
the `c` enciphered blocks after block `j` added (`hsum_add`).
-/

namespace VG.Proof.Ocb

open VG.Spec.Ocb (Block Cipher blockAt)

/-- `x` XORed with `g 0`, …, `g (k − 1)`. -/
def sumOf (x : Block) (g : Nat → Block) : Nat → Block
  | 0 => x
  | k + 1 => sumOf x g k ^^^ g k

theorem hsum_add (ciph : Cipher) (l : Block) (a : List Byte) (j : Nat) :
    ∀ c, hsum ciph l a (j + c) =
      sumOf (hsum ciph l a j) (fun k => ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1))) c
  | 0 => rfl
  | c + 1 => by rw [← Nat.add_assoc, hsum, hsum_add ciph l a j c]; rfl

end VG.Proof.Ocb
