module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # Starting RSA key generation on AArch64

`vg_rsa_generate_init(state = x0, bits = x1, e = x2, e_len = x3)`
(`VG.Spec.RsaKeyGen.keySearchInit`), as on x86-64
(`Impl/RsaKeyGen/X86_64/KeyInit.lean`): `e`'s value is read octet by octet,
keeping its low 32 bits and whether any bit above them is set; the status is
1, 2 for a size above 8192 bits or below 512 rounded down to a multiple of
128, or 0 (which overrides 2) for an exponent that is above 32 bits, even, or
1. The words are the first prime's counted candidates (`40 prime_len`, or
`64 prime_len` for `e = 3`), the primes' octets `prime_len = 8 (bits / 128)`,
the budget `32769 prime_len`, the first request `32 prime_len`, the phase 0,
the four generations and `e`'s eight octets, most significant first; or seven
zeros. Only the loop over `e`'s octets branches, on `e_len`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.AArch64.KeyInit

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- One octet of `e` (at `x2`): `x9` its value so far modulo `2^32`, `x10` the
OR of the bits shifted past them. -/
def octet : List Instr := [
  .ldrb .x11 .x2 0, .lsl .x .x9 .x9 8, .add .x .x9 .x9 .x11, .lsr .x .x12 .x9 32,
  .logic .orr .x .x10 .x10 .x12, .addImm .w .x9 .x9 0, .addImm .x .x2 .x2 1]

/-- `e`'s `e_len` (`x3`) octets. -/
def scan : Prog isa := .seq (.block [movi .x9 0, movi .x10 0])
  (.ite (.zero .x .x3) (.block []) (countLoop .x3 octet))

/-- The status in `x13`: 1, 2 for the size `bits` (`x1`), 0 for the exponent;
`x17` is 0 from here on. Each test is a subtraction's carry. -/
def statusSize : List Instr := [
  movi .x13 1, movi .x14 2, movi .x17 0,
  movi .x15 512, .subs .x .x16 .x1 .x15, .csel .x .x13 .x13 .x14,
  movi .x15 8193, .subs .x .x16 .x1 .x15, .csel .x .x13 .x14 .x13]

/-- 0 if any bit of `e` above 32 is set (`x10 ≠ 0`), if `e` is even, or if it
is at most 1. -/
def statusExponent : List Instr := [
  .subs .x .x16 .x17 .x10, .csel .x .x13 .x13 .x17,
  movi .x15 1, .logic .and .x .x16 .x9 .x15, .subs .x .x16 .x16 .x15, .csel .x .x13 .x13 .x17,
  .subs .x .x16 .x15 .x9, .csel .x .x13 .x17 .x13]

def status : List Instr := statusSize ++ statusExponent

/-- The words: `prime_len` in `x4`, the counted candidates in `x5`, the
budget in `x6`, the first request in `x7`, the generations in `x8`, `e`'s
octets in `x11`. -/
def compute : List Instr := [
  .lsr .x .x4 .x1 7, .lsl .x .x4 .x4 3,
  .lsl .x .x5 .x4 3, .lsl .x .x6 .x4 5, .add .x .x5 .x5 .x6, .lsl .x .x6 .x4 6,
  movi .x15 3, .logic .eor .x .x16 .x9 .x15, .subs .x .x16 .x17 .x16, .csel .x .x5 .x6 .x5,
  .lsl .x .x6 .x4 15, .add .x .x6 .x6 .x4, .lsl .x .x7 .x4 5, movi .x8 4, .rev .x11 .x9]

/-- Zeros (`x17`) unless the status is 1. -/
def mask : List Instr := [
  movi .x15 1, .logic .eor .x .x16 .x13 .x15, .subs .x .x16 .x17 .x16,
  .csel .x .x5 .x5 .x17, .csel .x .x4 .x4 .x17, .csel .x .x6 .x6 .x17, .csel .x .x7 .x7 .x17,
  .csel .x .x8 .x8 .x17, .csel .x .x11 .x11 .x17]

def stores : List Instr := [
  st .x5 .x0 0, st .x4 .x0 8, st .x6 .x0 16, st .x7 .x0 24, st .x17 .x0 32, st .x8 .x0 40,
  st .x11 .x0 48, mov .x0 .x13]

def words : List Instr := compute ++ mask ++ stores

def init : Prog isa := .seq scan (.block (status ++ words))

end VG.Impl.RsaKeyGen.AArch64.KeyInit
