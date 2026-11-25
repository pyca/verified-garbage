module

public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms

/-!
# Bitsliced AES states in 64-bit words, four blocks each

Slice `j` (a 64-bit word) holds bit `j` of every byte: the byte of row `r`
and column `c` of block `k` at position `k + 4 (c + 4 r)`. In form 1 of a
state (after a round that left ShiftRows out) that position holds the byte
of column `c - r`. The linear layers are given as the input bits each output
bit XORs; a bit is numbered `64 w + t`, for bit `t` of word `w`.
-/

@[expose] public section

namespace VG.Proof.Aes.Slices

/-- The position of the byte `n` (`r + 4 c`) of block `k` in form `f`. -/
def at_ (f : Bool) (n k : Nat) : Nat :=
  k + 4 * ((if f then (n / 4 + n % 4) % 4 else n / 4) + 4 * (n % 4))

/-- The byte, of a block, at position `p` in form `f`. -/
def byteAt (f : Bool) (p : Nat) : Nat :=
  p / 16 + 4 * (if f then (p / 4 % 4 + 4 - p / 16) % 4 else p / 4 % 4)

/-- `toBs`: from words `k + 4 c`, half `c` (columns `2 c`, `2 c + 1`) of block `k`. -/
def toBsG (j p : Nat) : List Nat :=
  [64 * (p % 4 + 4 * (byteAt false p / 8)) + (8 * (byteAt false p % 8) + j)]

/-- `fromBs`: to those words. -/
def fromBsG (w t : Nat) : List Nat := [64 * (t % 8) + at_ false (8 * (w / 4) + t / 8) (w % 4)]

/-- The bits of MixColumns' slice `j` of a byte from slice `j` of the byte (`a 0`)
and the next rows' (`a 1`, `a 2`, `a 3`), as (row offset, slice). -/
def mcTerms (j : Nat) : List (Nat × Nat) :=
  let two (i : Nat) : List (Nat × Nat) :=
    (if j = 0 then [] else [(i, j - 1)]) ++ (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [(i, 7)] else [])
  two 0 ++ two 1 ++ [(1, j), (2, j), (3, j)]

/-- The byte `i` rows after byte `n` in its column. -/
def down (n i : Nat) : Nat := (n % 4 + i) % 4 + 4 * (n / 4)

/-- MixColumns in form `f`. -/
def mcG (f : Bool) (j p : Nat) : List Nat :=
  (mcTerms j).map fun t => 64 * t.2 + at_ f (down (byteAt f p) t.1) (p % 4)

/-- ShiftRows' source of byte `n`. -/
def srSrc (n : Nat) : Nat := n % 4 + 4 * ((n / 4 + n % 4) % 4)

/-- ShiftRows twice (from form 1 to 0, with one left out; and back). -/
def sr2G (j p : Nat) : List Nat := [64 * j + at_ false (srSrc (srSrc (byteAt false p))) (p % 4)]

end VG.Proof.Aes.Slices
