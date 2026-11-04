module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # Starting the RSA prime search on AArch64

`vg_rsa_prime_search_init(state = x0, prime_len = x1, e = x2, e_len = x3)`
(`VG.Spec.RsaKeyGen.primeInit`), as on x86-64
(`Impl/RsaKeyGen/X86_64/SearchInit.lean`): for a width `prime_len` a
multiple of 8 in 32..=512 and an exponent of 1 to 8 octets, the counted
candidates allowed (`primeLimit`: `40 prime_len`, or `64 prime_len` for an
exponent of 3, with any leading zeros), `prime_len`, the entropy budget
`32769 prime_len` and the first request `32 prime_len`; otherwise four
zeros. The bounds are checked as in `Impl/Ffdh/AArch64/Generation/Init.lean`:
`x13 := 1` exactly when `32 ≤ prime_len < 513` and `1 ≤ e_len < 9`, each
bound by the carry of a subtraction made 0 or 1 by `csel`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.AArch64.SearchInit

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- `x13 := 32 ≤ prime_len < 513 ∧ 1 ≤ e_len < 9`, as 1 or 0. -/
def validate : List Instr := [
  movi .x11 0, movi .x12 1, movi .x9 32, .subs .x .x10 .x1 .x9, .csel .x .x13 .x12 .x11,
  movi .x9 513, .subs .x .x10 .x1 .x9, .csel .x .x14 .x11 .x12, .logic .and .x .x13 .x13 .x14,
  movi .x9 1, .subs .x .x10 .x3 .x9, .csel .x .x15 .x12 .x11, .logic .and .x .x13 .x13 .x15,
  movi .x9 9, .subs .x .x10 .x3 .x9, .csel .x .x16 .x11 .x12, .logic .and .x .x13 .x13 .x16]

/-- Zeros to the four words, and 0 returned. -/
def clear : List Instr := [
  movi .x9 0, st .x9 .x0 0, st .x9 .x0 8, st .x9 .x0 16, st .x9 .x0 24, movi .x0 0]

/-- `e` (`e_len` octets at `x2`, most significant first) into `x6`. -/
def loadE : Prog isa := .seq (.block [mov .x4 .x2, mov .x5 .x3, movi .x6 0])
  (countLoop .x5 [.lsl .x .x6 .x6 8, .ldrb .x7 .x4 0, .add .x .x6 .x6 .x7, .addImm .x .x4 .x4 1])

/-- The four words, for `prime_len` in `x1` and `e` in `x6`: the budget
`40 prime_len` (`5 · bits`), or `64 prime_len` (`8 · bits`) for `e = 3`;
and 1 returned. -/
def words : List Instr := [
  .subImm .x .x8 .x6 3, .tst .x .x8 .x8, .lsl .x .x9 .x1 3, .lsl .x .x10 .x9 2, .add .x .x10 .x10 .x9,
  .lsl .x .x11 .x1 6, .cselc .x .x10 .x11 .x10 .eq, .lsl .x .x12 .x1 15, .add .x .x12 .x12 .x1,
  .lsl .x .x13 .x1 5, st .x10 .x0 0, st .x1 .x0 8, st .x12 .x0 16, st .x13 .x0 24, movi .x0 1]

def initializeState : Prog isa := .seq loadE (.block words)

/-- The bounds, then whether `prime_len` is a multiple of 8. -/
def init : Prog isa := .seq (.block validate)
  (.ite (.zero .x .x13) (.block clear)
    (.seq (.block [movi .x9 7, .logic .and .x .x10 .x1 .x9])
      (.ite (.zero .x .x10) initializeState (.block clear))))

end VG.Impl.RsaKeyGen.AArch64.SearchInit
