import VerifiedGarbage.Impl.Aes.Circuit

/-!
# The SM4 S-box as a Boolean circuit

SM4's S-box is affine-equivalent to the AES S-box. Both invert in
GF(2⁸) between affine maps: SM4's `S(x) = A · (A x ⊕ C)⁻¹ ⊕ C` with the
field `x⁸ + x⁷ + x⁶ + x⁵ + x⁴ + x² + 1`, the cyclic matrix `A` and
`C = d3`; mapping that field to AES's (`x ↦ β`, for the root `β = 0x3e`
of SM4's polynomial in AES's field) gives `S(x) = A_out(S_AES(A_in(x)))`
for affine maps `A_in`, `A_out`. The circuit is that of
`Impl/Aes/Circuit.lean` (Boyar and Peralta's), with its top linear layer
composed with `A_in` and its bottom one with `A_out`, the two recomputed
as XOR networks (by Paar's greedy algorithm; a constant 1 by an `xnor`):
124 gates, 32 of them ANDs.

Applied to 64-bit words bit by bit, it computes 64 S-boxes at once. Its
inputs are numbered from the most significant bit: `x₀` is bit 7 and `x₇`
bit 0 (variables `0 … 7`); likewise the outputs `s₀ … s₇` (variables
`116 … 123`). Each target's proof checks the code made from it on all 256
inputs; nothing here needs to be trusted.
-/

namespace VG.Impl.Sm4.Circuit

open VG.Impl.Aes.Circuit

/-- The S-box circuit, from `x₀ … x₇` to `s₀ … s₇`. -/
def sbox : List Gate := [
  ⟨130, .xor, 3, 5⟩, ⟨131, .xor, 4, 7⟩, ⟨132, .xor, 6, 131⟩, ⟨133, .xor, 0, 130⟩,
  ⟨134, .xor, 2, 132⟩, ⟨135, .xor, 1, 5⟩, ⟨136, .xor, 0, 3⟩, ⟨137, .xor, 2, 133⟩,
  ⟨138, .xor, 1, 137⟩, ⟨139, .xor, 0, 4⟩, ⟨140, .xor, 1, 136⟩, ⟨141, .xor, 2, 130⟩,
  ⟨142, .xnor, 6, 137⟩, ⟨143, .xor, 131, 133⟩, ⟨144, .xor, 7, 140⟩, ⟨145, .xor, 134, 140⟩,
  ⟨146, .xor, 6, 135⟩, ⟨147, .xor, 1, 143⟩, ⟨148, .xnor, 7, 133⟩, ⟨149, .xor, 6, 139⟩,
  ⟨150, .xnor, 4, 141⟩, ⟨151, .xor, 132, 136⟩, ⟨152, .xor, 130, 134⟩, ⟨153, .xor, 134, 135⟩,
  ⟨154, .xnor, 0, 5⟩, ⟨155, .xnor, 6, 144⟩, ⟨156, .xor, 131, 141⟩, ⟨157, .xnor, 2, 139⟩,
  ⟨158, .xor, 6, 138⟩, ⟨159, .xnor, 130, 132⟩, ⟨160, .xnor, 0, 132⟩, ⟨32, .and, 158, 142⟩,
  ⟨33, .and, 134, 150⟩, ⟨34, .xor, 33, 32⟩, ⟨35, .and, 147, 149⟩, ⟨36, .xor, 35, 32⟩,
  ⟨37, .and, 6, 156⟩, ⟨38, .and, 135, 157⟩, ⟨39, .xor, 38, 37⟩, ⟨40, .and, 146, 148⟩,
  ⟨41, .xor, 40, 37⟩, ⟨42, .and, 151, 159⟩, ⟨43, .and, 138, 160⟩, ⟨44, .xor, 43, 42⟩,
  ⟨45, .and, 153, 133⟩, ⟨46, .xor, 45, 42⟩, ⟨47, .xor, 34, 44⟩, ⟨48, .xor, 36, 46⟩,
  ⟨49, .xor, 39, 44⟩, ⟨50, .xor, 41, 46⟩, ⟨51, .xor, 47, 154⟩, ⟨52, .xor, 48, 145⟩,
  ⟨53, .xor, 49, 152⟩, ⟨54, .xor, 50, 155⟩, ⟨55, .xor, 51, 52⟩, ⟨56, .and, 51, 53⟩,
  ⟨57, .xor, 54, 56⟩, ⟨58, .and, 55, 57⟩, ⟨59, .xor, 58, 52⟩, ⟨60, .xor, 53, 54⟩,
  ⟨61, .xor, 52, 56⟩, ⟨62, .and, 61, 60⟩, ⟨63, .xor, 62, 54⟩, ⟨64, .xor, 53, 63⟩,
  ⟨65, .xor, 57, 63⟩, ⟨66, .and, 54, 65⟩, ⟨67, .xor, 66, 64⟩, ⟨68, .xor, 57, 66⟩,
  ⟨69, .and, 59, 68⟩, ⟨70, .xor, 55, 69⟩, ⟨71, .xor, 70, 67⟩, ⟨72, .xor, 59, 63⟩,
  ⟨73, .xor, 59, 70⟩, ⟨74, .xor, 63, 67⟩, ⟨75, .xor, 72, 71⟩, ⟨98, .and, 74, 142⟩,
  ⟨99, .and, 67, 150⟩, ⟨100, .and, 63, 149⟩, ⟨101, .and, 73, 156⟩, ⟨102, .and, 70, 157⟩,
  ⟨103, .and, 59, 148⟩, ⟨104, .and, 72, 159⟩, ⟨105, .and, 75, 160⟩, ⟨106, .and, 71, 133⟩,
  ⟨107, .and, 74, 158⟩, ⟨108, .and, 67, 134⟩, ⟨109, .and, 63, 147⟩, ⟨110, .and, 73, 6⟩,
  ⟨111, .and, 70, 135⟩, ⟨112, .and, 59, 146⟩, ⟨113, .and, 72, 151⟩, ⟨114, .and, 75, 138⟩,
  ⟨115, .and, 71, 153⟩, ⟨170, .xor, 107, 113⟩, ⟨171, .xor, 104, 108⟩, ⟨172, .xor, 98, 103⟩,
  ⟨173, .xor, 111, 171⟩, ⟨174, .xor, 112, 173⟩, ⟨175, .xor, 99, 106⟩, ⟨176, .xor, 105, 174⟩,
  ⟨177, .xor, 115, 170⟩, ⟨178, .xor, 102, 172⟩, ⟨179, .xor, 176, 177⟩, ⟨180, .xor, 109, 178⟩,
  ⟨181, .xor, 114, 175⟩, ⟨182, .xor, 170, 181⟩, ⟨183, .xor, 101, 172⟩, ⟨184, .xor, 182, 183⟩,
  ⟨120, .xor, 109, 177⟩, ⟨186, .xor, 111, 114⟩, ⟨187, .xor, 110, 113⟩, ⟨188, .xor, 171, 178⟩,
  ⟨189, .xor, 175, 180⟩, ⟨122, .xnor, 174, 189⟩, ⟨191, .xor, 108, 184⟩, ⟨192, .xor, 100, 176⟩,
  ⟨123, .xnor, 105, 191⟩, ⟨116, .xnor, 186, 187⟩, ⟨195, .xor, 98, 99⟩, ⟨196, .xor, 101, 179⟩,
  ⟨118, .xor, 179, 195⟩, ⟨117, .xnor, 180, 192⟩, ⟨121, .xor, 102, 196⟩, ⟨119, .xnor, 182, 188⟩]

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def x (i : Nat) : Nat := i
def s (i : Nat) : Nat := 116 + i

end VG.Impl.Sm4.Circuit
