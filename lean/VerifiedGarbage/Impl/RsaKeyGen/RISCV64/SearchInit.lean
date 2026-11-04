module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul

/-! # Starting the RSA prime search on RISC-V

`vg_rsa_prime_search_init(state = a0, prime_len = a1, e = a2, e_len = a3)`
(`VG.Spec.RsaKeyGen.primeInit`), as on AArch64
(`Impl/RsaKeyGen/AArch64/SearchInit.lean`): for a width `prime_len` a
multiple of 8 in 32..=512 and an exponent of 1 to 8 octets, the counted
candidates allowed (`40 prime_len`, or `64 prime_len` for an exponent of 3,
with any leading zeros), `prime_len`, the entropy budget `32769 prime_len`
and the first request `32 prime_len`, and 1 returned; otherwise four zeros
and 0 returned. The comparisons are `sltu`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.RISCV64.SearchInit

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

/-- `t3 := 1` exactly when `32 ≤ prime_len ≤ 512`, `prime_len` is a
multiple of 8 and `1 ≤ e_len ≤ 8`, else 0. -/
def validate : List Instr := [
  .li .t0 32, .sltu .t1 .a1 .t0, .li .t0 513, .sltu .t2 .a1 .t0, .sub .t3 .t2 .t1,
  .logicImm .and .t1 .a1 7, .li .t0 1, .sltu .t1 .t1 .t0, .logic .and .t3 .t3 .t1,
  .sltu .t1 .a3 .t0, .li .t0 9, .sltu .t2 .a3 .t0, .sub .t1 .t2 .t1, .logic .and .t3 .t3 .t1]

/-- Zeros to the four words, and 0 returned. -/
def clear : List Instr := [
  .li .t0 0, .store .d .t0 .a0 0, .store .d .t0 .a0 8, .store .d .t0 .a0 16, .store .d .t0 .a0 24,
  .li .a0 0]

/-- Whether `e` (`a2`, `e_len` octets in `a3`) is 3: `t4` is 0 exactly
then, the OR of its leading octets and of its last octet XOR 3. -/
def isThree : Prog isa := .seq
  (.block [.li .t4 0, .addi .t5 .a3 (-1)])
  (.seq (.ite (.zero .t5) (.block [])
      (countLoop .t5 [.load .b .t6 .a2 0, .logic .or .t4 .t4 .t6, .addi .a2 .a2 1]))
    (.block [.load .b .t6 .a2 0, .li .t0 3, .logic .xor .t6 .t6 .t0, .logic .or .t4 .t4 .t6]))

/-- The four words, for `prime_len` in `a1`: the budget `40 prime_len`
(`5 · bits`), and `24 prime_len` more (`8 · bits`) when `t4` is 0, which
`t0 := t4 < 1`, 0 or 1, multiplies; then 1 returned. -/
def initializeState : List Instr := [
  .li .t0 1, .sltu .t0 .t4 .t0, .shift .sll .d .t1 .a1 3, .shift .sll .d .t2 .a1 5, .add .t1 .t1 .t2,
  .shift .sll .d .t2 .a1 4, .shift .sll .d .t5 .a1 3, .add .t2 .t2 .t5, .mul .t2 .t2 .t0, .add .t1 .t1 .t2,
  .store .d .t1 .a0 0, .store .d .a1 .a0 8, .shift .sll .d .t2 .a1 15, .add .t2 .t2 .a1, .store .d .t2 .a0 16,
  .shift .sll .d .t2 .a1 5, .store .d .t2 .a0 24, .li .a0 1]

def init : Prog isa := .seq (.block validate)
  (.ite (.zero .t3) (.block clear) (.seq isThree (.block initializeState)))

end VG.Impl.RsaKeyGen.RISCV64.SearchInit
