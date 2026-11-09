module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul

/-! # Starting RSA key generation on PPC64LE

`vg_rsa_generate_init(state = r3, bits = r4, e = r5, e_len = r6)`
(`VG.Spec.RsaKeyGen.keySearchInit`), as on x86-64
(`Impl/RsaKeyGen/X86_64/KeyInit.lean`): `e`'s value is read octet by octet,
keeping its low 32 bits and the OR of the bits shifted past them; the status
is 1, 2 for a size above 8192 bits or below 512, or 0 (which overrides 2)
for an exponent that is above 32 bits, even, or 1. The words are the first
prime's counted candidates (`40 prime_len`, or `64 prime_len` for `e = 3`),
the primes' octets `prime_len = 8 (bits / 128)`, the budget
`32769 prime_len`, the first request `32 prime_len`, the phase 0, the four
generations and `e`'s eight octets, most significant first; or seven zeros:
each word is the product of its value and the bit of the status 1.

As in the prime search's initialization
(`Impl/RsaKeyGen/PPC64LE/SearchInit.lean`), the comparisons are the sign bits
of differences of small numbers, without the carry bit: the size is first
split into `bits >> 14` and its low 14 bits. Only the loop over `e`'s octets
branches, on `e_len`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.PPC64LE.KeyInit

open VG VG.PPC64LE VG.Impl.Bignum.PPC64LE

/-- One octet of `e` (at `r5`): `r9` its value so far modulo `2^32`, `r10`
the OR of the bits shifted past them. -/
def octet : List Instr := [
  .lbz .r11 .r5 0, .lsl .r9 .r9 8, .add .r9 .r9 .r11, .lsr .d .r7 .r9 32, .logic .or .r10 .r10 .r7,
  .lsr .w .r9 .r9 0, .addi .r5 .r5 1]

/-- `e`'s `e_len` (`r6`) octets. -/
def scan : Prog isa := .seq (.block [.li .r9 0, .li .r10 0])
  (.ite (.zero .d .r6) (.block []) (countLoop .r6 octet))

/-- `d := 1` if `n < c`, else 0, for `n` and `c` below `2^63`, through `r12`. -/
def lt (d n : Reg) (c : Nat) : List Instr := [.li .r12 c, .sub d n .r12, .lsr .d d d 63]

/-- `r7`: 1 exactly for a valid exponent (no bits past the low 32 in `r10`,
and its low 32 bits `r9` odd and at least 3). -/
def expValid : List Instr :=
  lt .r7 .r10 1 ++ ([.li .r8 1, .logic .and .r8 .r9 .r8, .logic .and .r7 .r7 .r8] : List Instr) ++
    lt .r8 .r9 3 ++ ([.li .r12 1, .sub .r8 .r12 .r8, .logic .and .r7 .r7 .r8] : List Instr)

/-- `r8`: 1 exactly for a valid size (`bits` in `r4` below `2^14`, and its
low 14 bits from 512 to 8192). -/
def sizeValid : List Instr :=
  ([.lsr .d .r8 .r4 14] : List Instr) ++ lt .r8 .r8 1 ++
    ([.li .r12 16383, .logic .and .r11 .r4 .r12] : List Instr) ++ lt .r0 .r11 8193 ++ lt .r11 .r11 512 ++
    ([.sub .r0 .r0 .r11, .mul .r8 .r8 .r0] : List Instr)

/-- The status in `r12`, `r7 (2 − r8)`, and its bit of 1 in `r11`,
`r7 r8`. -/
def status : List Instr := [.li .r12 2, .sub .r12 .r12 .r8, .mul .r12 .r12 .r7, .mul .r11 .r7 .r8]

/-- The words, each times the bit in `r11`: the primes' octets in `r4`, the
counted candidates in `r5`, `r0` 1 exactly for `e = 3`. -/
def words : List Instr := [
  .lsr .d .r4 .r4 7, .lsl .r4 .r4 3,
  .li .r10 3, .logic .xor .r0 .r9 .r10, .li .r10 1, .sub .r0 .r0 .r10, .lsr .d .r0 .r0 63,
  .lsl .r5 .r4 3, .lsl .r6 .r4 5, .add .r5 .r5 .r6, .lsl .r6 .r4 4, .lsl .r7 .r4 3, .add .r6 .r6 .r7,
  .mul .r6 .r6 .r0, .add .r5 .r5 .r6,
  .mul .r5 .r5 .r11, .store .d .r5 .r3 0,
  .mul .r6 .r4 .r11, .store .d .r6 .r3 8,
  .lsl .r6 .r4 15, .add .r6 .r6 .r4, .mul .r6 .r6 .r11, .store .d .r6 .r3 16,
  .lsl .r6 .r4 5, .mul .r6 .r6 .r11, .store .d .r6 .r3 24,
  .li .r6 0, .store .d .r6 .r3 32,
  .lsl .r6 .r11 2, .store .d .r6 .r3 40,
  .mul .r6 .r9 .r11, .li .r7 48, .storeRev .d .r6 .r3 .r7]

def init : Prog isa := .seq scan (.block (expValid ++ sizeValid ++ status ++ words ++ [.addi .r3 .r12 0]))

end VG.Impl.RsaKeyGen.PPC64LE.KeyInit
