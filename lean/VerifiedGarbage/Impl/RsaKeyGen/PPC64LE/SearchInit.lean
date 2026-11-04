module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul

/-! # Starting the RSA prime search on PPC64LE

`vg_rsa_prime_search_init(state = r3, prime_len = r4, e = r5, e_len = r6)`
(`VG.Spec.RsaKeyGen.primeInit`), as on AArch64
(`Impl/RsaKeyGen/AArch64/SearchInit.lean`): for a width `prime_len` a
multiple of 8 in 32..=512 and an exponent of 1 to 8 octets, the counted
candidates allowed (`40 prime_len`, or `64 prime_len` for an exponent of 3,
with any leading zeros), `prime_len`, the entropy budget `32769 prime_len`
and the first request `32 prime_len`, and 1 returned; otherwise four zeros
and 0 returned.

As in the FFDH initializations (`Impl/Ffdh/PPC64LE/Generation/Init.lean`),
the comparisons are the sign bits of differences of small numbers, without
the carry bit: `prime_len` and `e_len` are first checked to be below
`2^14`, a branch on public values; then `lt c`, the sign bit of `x − c`, is
1 exactly when `x < c`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.PPC64LE.SearchInit

open VG VG.PPC64LE VG.Impl.Bignum.PPC64LE

/-- `r12 := (prime_len >> 14) | (e_len >> 14)`, zero exactly when both are
below `2^14`. -/
def high : List Instr := [.lsr .d .r12 .r4 14, .lsr .d .r11 .r6 14, .logic .or .r12 .r12 .r11]

/-- `d := 1` if `n < c`, else 0, for `n` and `c` below `2^63`, through `r9`. -/
def lt (d n : Reg) (c : Nat) : List Instr := [.li .r9 c, .sub d n .r9, .lsr .d d d 63]

/-- With both below `2^14`: `r12 := 1` exactly when `32 ≤ prime_len ≤ 512`,
`prime_len` is a multiple of 8 and `1 ≤ e_len ≤ 8`, else 0. -/
def validate : List Instr :=
  lt .r10 .r4 32 ++ lt .r11 .r4 513 ++ ([.sub .r12 .r11 .r10, .li .r9 7, .logic .and .r10 .r4 .r9] : List Instr) ++
    lt .r10 .r10 1 ++ ([.logic .and .r12 .r12 .r10] : List Instr) ++ lt .r7 .r6 1 ++ lt .r8 .r6 9 ++
    ([.sub .r7 .r8 .r7, .logic .and .r12 .r12 .r7] : List Instr)

/-- Zeros to the four words, and 0 returned. -/
def clear : List Instr := [
  .li .r9 0, .store .d .r9 .r3 0, .store .d .r9 .r3 8, .store .d .r9 .r3 16, .store .d .r9 .r3 24,
  .li .r3 0]

/-- Whether `e` (`r5`, `e_len` octets in `r6`) is 3: `r9` is 0 exactly
then, the OR of its leading octets and of its last octet XOR 3. -/
def isThree : Prog isa := .seq
  (.block [.li .r9 0, .subi .r10 .r6 1])
  (.seq (.ite (.zero .d .r10) (.block [])
      (countLoop .r10 [.lbz .r11 .r5 0, .logic .or .r9 .r9 .r11, .addi .r5 .r5 1]))
    (.block [.lbz .r11 .r5 0, .li .r12 3, .logic .xor .r11 .r11 .r12, .logic .or .r9 .r9 .r11]))

/-- The four words, for `prime_len` in `r4`: the budget `40 prime_len`
(`5 · bits`), and `24 prime_len` more (`8 · bits`) when `r9` is 0, which
`r12`, the sign bit of `r9 − 1` (0 or 1), multiplies; then 1 returned. -/
def initializeState : List Instr := [
    .li .r12 1, .sub .r12 .r9 .r12, .lsr .d .r12 .r12 63, .lsl .r10 .r4 3, .lsl .r11 .r4 5, .add .r10 .r10 .r11, .lsl .r11 .r4 4, .lsl .r7 .r4 3,
    .add .r11 .r11 .r7, .mul .r11 .r11 .r12, .add .r10 .r10 .r11, .store .d .r10 .r3 0, .store .d .r4 .r3 8,
    .lsl .r11 .r4 15, .add .r11 .r11 .r4, .store .d .r11 .r3 16, .lsl .r11 .r4 5, .store .d .r11 .r3 24,
    .li .r3 1]

def init : Prog isa :=
  .seq (.block high)
    (.ite (.zero .d .r12)
      (.seq (.block validate) (.ite (.zero .d .r12) (.block clear) (.seq isThree (.block initializeState))))
      (.block clear))

end VG.Impl.RsaKeyGen.PPC64LE.SearchInit
