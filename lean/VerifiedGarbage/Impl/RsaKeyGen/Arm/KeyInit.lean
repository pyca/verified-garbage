module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Starting RSA key generation on ARMv7

`vg_rsa_generate_init(state = r0, bits = r1, e = r2, e_len = r3)`
(`VG.Spec.RsaKeyGen.keySearchInit`), as on x86-64
(`Impl/RsaKeyGen/X86_64/KeyInit.lean`): `e`'s value is read octet by octet,
keeping its low 32 bits (`r4`) and the OR of the bits shifted past them
(`r5`); the callee's `r4` and `r5` wait in the state, in high halves that
end zero (the contract grants no stack). The status is 1, 2 for a size
above 8192 bits or below 512 rounded down to a multiple of 128, or 0 (which
overrides 2) for an exponent that is above 32 bits, even, or 1. The words
are the first prime's counted candidates (`40 prime_len`, or `64 prime_len`
for `e = 3`), the primes' octets `prime_len = 8 (bits / 128)`, the budget
`32769 prime_len`, the first request `32 prime_len`, the phase 0, the four
generations and `e`'s eight octets, most significant first, each `u64` as
two 32-bit stores; or zeros, every value masked by the status. Only the loop
over `e`'s octets branches, on `e_len`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.Arm.KeyInit

open VG VG.Arm

/-- One octet of `e` (at `r2`). -/
def octet : List Instr := [
  .ldrb .r12 .r2 0, .dp .orr .r5 .r5 (.shifted .r4 .lsr 24), .mov .r4 (.shifted .r4 .lsl 8),
  .dp .add .r4 .r4 (.reg .r12), .dp .add .r2 .r2 (.imm 1), .subs .r3 .r3 (.imm 1)]

/-- `e`'s `e_len` (`r3`) octets. -/
def scan : Prog isa := .seq (.block [.mov .r4 (.imm 0), .mov .r5 (.imm 0), .cmp .r3 (.imm 0)])
  (.ite .eq (.block []) (.loop (.block octet) .ne))

/-- The status in `r5` (0, 1 or 2), and in `r12` the mask of status 1: all
ones or zero. Each test is a comparison's carry: `r3 = [bits ≥ 512] −
[bits ≥ 8193]` the size's validity, `r12` the exponent's (odd, at least 3,
nothing above 32 bits). -/
def sizeTest : List Instr := [
  .cmp .r1 (.imm 512), .mov .r3 (.imm 0), .adc .r3 .r3 (.imm 0),
  .movw .r12 8193, .cmp .r1 (.reg .r12), .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0),
  .dp .sub .r3 .r3 (.reg .r12)]

def expTest : List Instr := [
  .dp .and .r12 .r4 (.imm 1),
  .cmp .r4 (.imm 3), .mov .r2 (.imm 0), .adc .r2 .r2 (.imm 0), .dp .and .r12 .r12 (.reg .r2),
  .subs .r2 .r5 (.imm 1), .mov .r2 (.imm 0), .adc .r2 .r2 (.imm 0), .dp .bic .r12 .r12 (.reg .r2)]

def statusMask : List Instr := [
  .mov .r5 (.imm 2), .dp .sub .r5 .r5 (.reg .r3), .mul .r5 .r5 .r12,
  .dp .and .r12 .r12 (.reg .r3), .mov .r3 (.imm 0), .dp .sub .r12 .r3 (.reg .r12)]

def status : List Instr := sizeTest ++ expTest ++ statusMask

/-- The words, each masked by `r12`: `prime_len` in `r2`; the high halves,
the phase and the high half of the generations zero (`r3`); the generations
4; `prime_len`; the budget; the first request; `e`'s octets (its low word,
byte-reversed, at `state + 52`, after four zeros); and the counted
candidates `64 prime_len - 24 prime_len · [e ≠ 3]`. -/
def wordsZero : List Instr := [
  .mov .r2 (.shifted .r1 .lsr 7), .mov .r2 (.shifted .r2 .lsl 3),
  .str .r3 .r0 4, .str .r3 .r0 28, .str .r3 .r0 32, .str .r3 .r0 36, .str .r3 .r0 44, .str .r3 .r0 48]

def wordsSmall : List Instr := [
  .mov .r1 (.imm 4), .dp .and .r1 .r1 (.reg .r12), .str .r1 .r0 40,
  .dp .and .r1 .r2 (.reg .r12), .str .r1 .r0 8]

def wordsBig : List Instr := [
  .mov .r1 (.shifted .r2 .lsl 15), .dp .add .r1 .r1 (.reg .r2), .dp .and .r1 .r1 (.reg .r12), .str .r1 .r0 16,
  .mov .r1 (.shifted .r2 .lsl 5), .dp .and .r1 .r1 (.reg .r12), .str .r1 .r0 24,
  .rev .r1 .r4, .dp .and .r1 .r1 (.reg .r12), .str .r1 .r0 52]

def limitFlag : List Instr := [
  .dp .eor .r1 .r4 (.imm 3), .subs .r1 .r1 (.imm 1), .mov .r1 (.imm 0), .adc .r1 .r1 (.imm 0)]

def limitStore : List Instr := [
  .mov .r3 (.shifted .r2 .lsl 3), .dp .add .r3 .r3 (.shifted .r2 .lsl 4), .mul .r1 .r1 .r3,
  .mov .r3 (.shifted .r2 .lsl 6), .dp .sub .r3 .r3 (.reg .r1), .dp .and .r3 .r3 (.reg .r12), .str .r3 .r0 0]

def wordsLimit : List Instr := limitFlag ++ limitStore

def words : List Instr := wordsZero ++ wordsSmall ++ wordsBig ++ wordsLimit

/-- The caller's `r4` and `r5` saved in the state's halves 3 and 5. -/
def save : List Instr := [.str .r4 .r0 12, .str .r5 .r0 20]

/-- `r4` and `r5` restored, zeros to their halves, and the status returned. -/
def restore : List Instr := [
  .mov .r1 (.reg .r5), .ldr .r4 .r0 12, .ldr .r5 .r0 20, .mov .r2 (.imm 0), .str .r2 .r0 12,
  .str .r2 .r0 20, .mov .r0 (.reg .r1)]

def init : Prog isa := .seq (.block save) (.seq scan (.block (status ++ words ++ restore)))

end VG.Impl.RsaKeyGen.Arm.KeyInit
