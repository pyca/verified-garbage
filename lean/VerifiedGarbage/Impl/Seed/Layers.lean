module

/-!
# SEED's S-boxes through AES's

Untrusted. With the isomorphism `M` from SEED's field `GF(2)[x]/(x⁸ + x⁶ + x⁵
+ x + 1)` (in which RFC 4269's S-boxes are affine functions of powers of the
inverse) to AES's, `M(x) = Σᵢ xᵢ αⁱ` for the root `α = 0x19` of SEED's
polynomial in AES's field, both S-boxes are affine functions of the AES
S-box: `S0(x) = P0(S_AES(M x)) ⊕ 0xE7` and `S1(x) = P1(S_AES(M x)) ⊕ 0x2B`
for linear maps `P0` and `P1`. `Proof/Seed/Sbox.lean` checks both on all
256 inputs; nothing here needs to be trusted.

A linear map is given by its rows: output bit `j` is the XOR of the input
bits `rows[j]` (bit 0 the least significant).
-/

@[expose] public section

namespace VG.Impl.Seed

def mRows : List (List Nat) :=
  [[0, 1, 3], [2, 3, 6, 7], [4, 5, 7], [1, 2, 3, 5], [1, 2, 4], [3, 4], [2, 3, 4, 5], [4, 5, 6]]

def p0Rows : List (List Nat) :=
  [[2, 4, 5, 6], [2, 4, 6, 7], [0, 1, 4, 6], [0, 2, 4, 5, 6, 7], [0, 2, 3, 4, 6],
   [0, 1, 3, 5, 6], [0, 4, 5, 6], [1, 3, 6, 7]]

def p1Rows : List (List Nat) :=
  [[1, 3], [1, 4, 5, 6, 7], [0, 2, 3, 4, 6], [0, 1, 3, 4, 5, 6], [3, 6, 7], [3, 4, 5, 6],
   [1, 2, 3, 6], [3]]

/-- The rows of `P0` (for `X0` and `X2`) or `P1` (for `X1` and `X3`). -/
def pRows (odd : Bool) : List (List Nat) := if odd then p1Rows else p0Rows

/-- The constants: `S0`'s and `S1`'s. -/
def sConst (odd : Bool) : BitVec 8 := if odd then 0x2B else 0xE7

/-- The constant part of `G`, in both halves of a 64-bit word: its mixing
of the S-boxes' constants `0xE7, 0x2B, 0xE7, 0x2B`. -/
def gConst : BitVec 64 := 0xE72BE72BE72BE72B

end VG.Impl.Seed
