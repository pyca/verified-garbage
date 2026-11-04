module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # Starting the RSA prime search on AArch64

`vg_rsa_prime_search_init(state = x0, prime_len = x1, e = x2, e_len = x3)`
(`VG.Spec.RsaKeyGen.primeInit`), as on x86-64
(`Impl/RsaKeyGen/X86_64/SearchInit.lean`): for a width `prime_len` a
multiple of 8 in 32..=512 and an exponent of 1 to 8 octets, the counted
candidates allowed (`40 prime_len`, or `64 prime_len` for an exponent of 3,
with any leading zeros), `prime_len`, the entropy budget `32769 prime_len`
and the first request `32 prime_len`, and 1 returned; otherwise four zeros
and 0 returned.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.AArch64.SearchInit

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- `x13 := 1` exactly when `32 ≤ prime_len < 513`, `prime_len` is a
multiple of 8 and `1 ≤ e_len < 9`, by the carries of subtractions; 0
otherwise. -/
def validate : List Instr := [
  movi .x11 0, movi .x12 1,
  movi .x9 32, .subs .x .x10 .x1 .x9, .csel .x .x13 .x12 .x11,
  movi .x9 513, .subs .x .x10 .x1 .x9, .csel .x .x14 .x11 .x12, .logic .and .x .x13 .x13 .x14,
  movi .x9 7, .logic .and .x .x10 .x1 .x9, .subs .x .x10 .x11 .x10, .csel .x .x14 .x12 .x11,
  .logic .and .x .x13 .x13 .x14,
  movi .x9 1, .subs .x .x10 .x3 .x9, .csel .x .x14 .x12 .x11, .logic .and .x .x13 .x13 .x14,
  movi .x9 9, .subs .x .x10 .x3 .x9, .csel .x .x14 .x11 .x12, .logic .and .x .x13 .x13 .x14]

/-- Zeros to the four words, and 0 returned. -/
def clear : List Instr := [
  movi .x9 0, st .x9 .x0 0, st .x9 .x0 8, st .x9 .x0 16, st .x9 .x0 24, movi .x0 0]

/-- Whether `e` (`x2`, `e_len` octets in `x3`) is 3: `x9` is 0 exactly
then, the OR of its leading octets and of its last octet XOR 3. -/
def isThree : Prog isa := .seq
  (.block [movi .x9 0, .subImm .x .x10 .x3 1])
  (.seq (.ite (.zero .x .x10) (.block [])
      (countLoop .x10 [.ldrb .x11 .x2 0, .logic .orr .x .x9 .x9 .x11, .addImm .x .x2 .x2 1]))
    (.block [.ldrb .x11 .x2 0, movi .x12 3, .logic .eor .x .x11 .x11 .x12,
      .logic .orr .x .x9 .x9 .x11]))

/-- The four words, for `prime_len` in `x1`: the budget `40 prime_len`
(`5 · bits`), or `64 prime_len` (`8 · bits`) when `x9` is 0; then 1
returned. -/
def initializeState : List Instr := [
  .lsl .x .x10 .x1 3, .lsl .x .x11 .x1 5, .add .x .x10 .x10 .x11, .lsl .x .x12 .x1 6,
  movi .x11 0, .subs .x .x11 .x11 .x9, .csel .x .x10 .x12 .x10, st .x10 .x0 0, st .x1 .x0 8,
  .lsl .x .x11 .x1 15, .add .x .x11 .x11 .x1, st .x11 .x0 16, .lsl .x .x11 .x1 5, st .x11 .x0 24,
  movi .x0 1]

def init : Prog isa := .seq (.block validate)
  (.ite (.zero .x .x13) (.block clear) (.seq isThree (.block initializeState)))

end VG.Impl.RsaKeyGen.AArch64.SearchInit
