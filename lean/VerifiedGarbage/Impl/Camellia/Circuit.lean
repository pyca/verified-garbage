import VerifiedGarbage.Impl.Aes.Circuit

/-!
# The Camellia S-box as a Boolean circuit

Camellia's `SBOX1` is affine-equivalent to the AES S-box:
`SBOX1(x) = A_out(S_AES(A_in(x)))` for the affine maps `A_in` (linear part
with columns `ad 05 6b 0e 51 f1 8a 09`, bit 0 first, and constant `45`) and
`A_out` (columns `f0 f3 0e e0 f9 86 d7 a4`, constant `3c`), the
decomposition that Linux's `camellia-aesni-avx-asm_64.S` uses with AES-NI.
The circuit is that of `Impl/Aes/Circuit.lean` (Boyar and Peralta's), with
its top linear layer composed with `A_in`, its bottom one with `A_out`,
and the two recomputed as XOR networks (by Paar's greedy algorithm; a
constant 1 by an `xnor`): 134 gates, 32 of them ANDs.

Applied to 64-bit words bit by bit, it computes 64 S-boxes at once. Its
inputs are numbered from the most significant bit: `x₀` is bit 7 and `x₇`
bit 0 (variables `0 … 7`); likewise the outputs `s₀ … s₇` (variables
`116 … 123`). Each target's proof checks the code made from it on all 256
inputs; nothing here needs to be trusted.
-/

namespace VG.Impl.Camellia.Circuit

open VG.Impl.Aes.Circuit

/-- The S-box circuit: `SBOX1`, from `x₀ … x₇` to `s₀ … s₇`. -/
def sbox : List Gate := [
  ⟨130, .xor, 0, 6⟩, ⟨131, .xor, 2, 4⟩, ⟨132, .xor, 5, 130⟩, ⟨133, .xor, 1, 7⟩,
  ⟨134, .xor, 7, 131⟩, ⟨135, .xor, 3, 6⟩, ⟨136, .xor, 3, 132⟩, ⟨137, .xor, 1, 131⟩,
  ⟨138, .xor, 5, 133⟩, ⟨139, .xor, 132, 133⟩, ⟨140, .xor, 0, 1⟩, ⟨141, .xnor, 0, 133⟩,
  ⟨142, .xor, 1, 4⟩, ⟨143, .xor, 2, 6⟩, ⟨144, .xor, 2, 7⟩, ⟨145, .xor, 2, 132⟩,
  ⟨146, .xor, 3, 133⟩, ⟨147, .xor, 3, 140⟩, ⟨148, .xnor, 4, 7⟩, ⟨149, .xor, 5, 134⟩,
  ⟨150, .xnor, 5, 135⟩, ⟨151, .xnor, 6, 137⟩, ⟨152, .xor, 130, 134⟩, ⟨153, .xor, 130, 137⟩,
  ⟨154, .xor, 131, 135⟩, ⟨155, .xor, 131, 136⟩, ⟨156, .xor, 131, 139⟩, ⟨157, .xnor, 132, 134⟩,
  ⟨158, .xnor, 132, 142⟩, ⟨159, .xnor, 134, 135⟩, ⟨160, .xnor, 136, 144⟩, ⟨161, .xnor, 138, 143⟩,
  ⟨162, .xnor, 138, 154⟩, ⟨163, .xnor, 0, 1⟩, ⟨164, .xor, 163, 1⟩, ⟨165, .xnor, 0, 6⟩,
  ⟨32, .and, 150, 147⟩, ⟨33, .and, 164, 161⟩, ⟨34, .xor, 33, 32⟩, ⟨35, .and, 136, 160⟩,
  ⟨36, .xor, 35, 32⟩, ⟨37, .and, 149, 157⟩, ⟨38, .and, 153, 145⟩, ⟨39, .xor, 38, 37⟩,
  ⟨40, .and, 139, 148⟩, ⟨41, .xor, 40, 37⟩, ⟨42, .and, 146, 155⟩, ⟨43, .and, 159, 162⟩,
  ⟨44, .xor, 43, 42⟩, ⟨45, .and, 151, 141⟩, ⟨46, .xor, 45, 42⟩, ⟨47, .xor, 34, 44⟩,
  ⟨48, .xor, 36, 46⟩, ⟨49, .xor, 39, 44⟩, ⟨50, .xor, 41, 46⟩, ⟨51, .xor, 47, 156⟩,
  ⟨52, .xor, 48, 152⟩, ⟨53, .xor, 49, 165⟩, ⟨54, .xor, 50, 158⟩, ⟨55, .xor, 51, 52⟩,
  ⟨56, .and, 51, 53⟩, ⟨57, .xor, 54, 56⟩, ⟨58, .and, 55, 57⟩, ⟨59, .xor, 58, 52⟩,
  ⟨60, .xor, 53, 54⟩, ⟨61, .xor, 52, 56⟩, ⟨62, .and, 61, 60⟩, ⟨63, .xor, 62, 54⟩,
  ⟨64, .xor, 53, 63⟩, ⟨65, .xor, 57, 63⟩, ⟨66, .and, 54, 65⟩, ⟨67, .xor, 66, 64⟩,
  ⟨68, .xor, 57, 66⟩, ⟨69, .and, 59, 68⟩, ⟨70, .xor, 55, 69⟩, ⟨71, .xor, 70, 67⟩,
  ⟨72, .xor, 59, 63⟩, ⟨73, .xor, 59, 70⟩, ⟨74, .xor, 63, 67⟩, ⟨75, .xor, 72, 71⟩,
  ⟨98, .and, 74, 147⟩, ⟨99, .and, 67, 161⟩, ⟨100, .and, 63, 160⟩, ⟨101, .and, 73, 157⟩,
  ⟨102, .and, 70, 145⟩, ⟨103, .and, 59, 148⟩, ⟨104, .and, 72, 155⟩, ⟨105, .and, 75, 162⟩,
  ⟨106, .and, 71, 141⟩, ⟨107, .and, 74, 150⟩, ⟨108, .and, 67, 164⟩, ⟨109, .and, 63, 136⟩,
  ⟨110, .and, 73, 149⟩, ⟨111, .and, 70, 153⟩, ⟨112, .and, 59, 139⟩, ⟨113, .and, 72, 146⟩,
  ⟨114, .and, 75, 159⟩, ⟨115, .and, 71, 151⟩, ⟨170, .xor, 99, 105⟩, ⟨171, .xor, 101, 103⟩,
  ⟨172, .xor, 104, 106⟩, ⟨173, .xor, 98, 114⟩, ⟨174, .xor, 109, 170⟩, ⟨175, .xor, 110, 171⟩,
  ⟨176, .xor, 113, 172⟩, ⟨177, .xor, 100, 112⟩, ⟨178, .xor, 104, 115⟩, ⟨179, .xor, 106, 107⟩,
  ⟨180, .xor, 107, 108⟩, ⟨181, .xor, 111, 175⟩, ⟨182, .xor, 114, 176⟩, ⟨183, .xor, 173, 174⟩,
  ⟨184, .xor, 98, 100⟩, ⟨185, .xor, 99, 102⟩, ⟨186, .xor, 103, 173⟩, ⟨187, .xor, 108, 178⟩,
  ⟨188, .xor, 110, 174⟩, ⟨189, .xor, 113, 170⟩, ⟨190, .xor, 115, 179⟩, ⟨191, .xor, 171, 180⟩,
  ⟨119, .xor, 172, 184⟩, ⟨193, .xor, 175, 177⟩, ⟨194, .xor, 176, 180⟩, ⟨195, .xor, 177, 179⟩,
  ⟨196, .xor, 178, 189⟩, ⟨123, .xor, 181, 182⟩, ⟨198, .xor, 181, 183⟩, ⟨118, .xnor, 182, 191⟩,
  ⟨121, .xnor, 183, 187⟩, ⟨201, .xor, 185, 186⟩, ⟨120, .xnor, 188, 195⟩, ⟨122, .xnor, 190, 198⟩,
  ⟨116, .xor, 193, 196⟩, ⟨117, .xnor, 194, 201⟩]

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`. -/
def x (i : Nat) : Nat := i
def s (i : Nat) : Nat := 116 + i

end VG.Impl.Camellia.Circuit
