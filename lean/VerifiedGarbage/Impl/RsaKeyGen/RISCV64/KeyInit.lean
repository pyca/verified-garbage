module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul
public import VerifiedGarbage.Impl.Words.RISCV64

/-! # Starting RSA key generation on RISC-V

`vg_rsa_generate_init(state = a0, bits = a1, e = a2, e_len = a3)`
(`VG.Spec.RsaKeyGen.keySearchInit`), as on PPC64LE
(`Impl/RsaKeyGen/PPC64LE/KeyInit.lean`): `e`'s value is read octet by octet,
keeping its low 32 bits (in `t3`) and the OR of the bits shifted past them
(in `t4`); the status is 1, 2 for a size above 8192 bits or below 512, or 0
(which overrides 2) for an exponent that is above 32 bits, even, or 1. The
words are the first prime's counted candidates (`40 prime_len`, or
`64 prime_len` for `e = 3`), the primes' octets `prime_len = 8 (bits / 128)`,
the budget `32769 prime_len`, the first request `32 prime_len`, the phase 0,
the four generations and `e`'s eight octets, most significant first (a byte
at a time, `storeBE`); or seven zeros: each word is the product of its value
and the bit of the status 1. The comparisons are `sltu`; only the loop over
`e`'s octets branches, on `e_len`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.RISCV64.KeyInit

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

/-- One octet of `e` (at `a2`): `t3` its value so far modulo `2^32`, `t4`
the OR of the bits shifted past them. -/
def octet : List Instr := [
  .load .b .t1 .a2 0, .shift .sll .d .t3 .t3 8, .add .t3 .t3 .t1, .shift .srl .d .t0 .t3 32,
  .logic .or .t4 .t4 .t0, .shift .sll .d .t3 .t3 32, .shift .srl .d .t3 .t3 32, .addi .a2 .a2 1]

/-- `e`'s `e_len` (`a3`) octets. -/
def scan : Prog isa := .seq (.block [.li .t3 0, .li .t4 0])
  (.ite (.zero .a3) (.block []) (countLoop .a3 octet))

/-- `t5`: 1 exactly for a valid exponent (no bits past the low 32 in `t4`,
and its low 32 bits `t3` odd and at least 3). -/
def expValid : List Instr := [
  .li .t0 1, .sltu .t5 .t4 .t0, .logicImm .and .t0 .t3 1, .logic .and .t5 .t5 .t0,
  .li .t0 3, .sltu .t0 .t3 .t0, .logicImm .xor .t0 .t0 1, .logic .and .t5 .t5 .t0]

/-- `t6`: 1 exactly for a valid size (`bits` in `a1` from 512 to 8192). -/
def sizeValid : List Instr := [
  .li .t0 1, .shift .sll .d .t0 .t0 13, .addi .t0 .t0 1, .sltu .t6 .a1 .t0,
  .li .t0 512, .sltu .t0 .a1 .t0, .logicImm .xor .t0 .t0 1, .logic .and .t6 .t6 .t0]

/-- The status in `t2`, `t5 (2 − t6)`, and its bit of 1 in `t1`, `t5 t6`. -/
def status : List Instr := [.li .t2 2, .sub .t2 .t2 .t6, .mul .t2 .t2 .t5, .mul .t1 .t5 .t6]

/-- The words, each times the bit in `t1`: the primes' octets in `a1`, the
counted candidates in `a4`, `t0` 1 exactly for `e = 3`. -/
def words : List Instr := [
  .shift .srl .d .a1 .a1 7, .shift .sll .d .a1 .a1 3,
  .logicImm .xor .t0 .t3 3, .li .a3 1, .sltu .t0 .t0 .a3,
  .shift .sll .d .a4 .a1 3, .shift .sll .d .a5 .a1 5, .add .a4 .a4 .a5,
  .shift .sll .d .a5 .a1 4, .shift .sll .d .a6 .a1 3, .add .a5 .a5 .a6,
  .mul .a5 .a5 .t0, .add .a4 .a4 .a5,
  .mul .a4 .a4 .t1, .store .d .a4 .a0 0,
  .mul .a5 .a1 .t1, .store .d .a5 .a0 8,
  .shift .sll .d .a5 .a1 15, .add .a5 .a5 .a1, .mul .a5 .a5 .t1, .store .d .a5 .a0 16,
  .shift .sll .d .a5 .a1 5, .mul .a5 .a5 .t1, .store .d .a5 .a0 24,
  .li .a5 0, .store .d .a5 .a0 32,
  .shift .sll .d .a5 .t1 2, .store .d .a5 .a0 40,
  .mul .a5 .t3 .t1] ++ Impl.Words.RISCV64.storeBE 8 .a5 .a6 .a0 48

def init : Prog isa := .seq scan (.block (expValid ++ sizeValid ++ status ++ words ++ [.addi .a0 .t2 0]))

end VG.Impl.RsaKeyGen.RISCV64.KeyInit
