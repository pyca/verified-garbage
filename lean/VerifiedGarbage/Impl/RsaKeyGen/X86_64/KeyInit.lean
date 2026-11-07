module

public import VerifiedGarbage.TCB.X86_64.Isa

/-! # Starting RSA key generation on x86-64

`vg_rsa_generate_init(state, bits, e, e_len)`
(`VG.Spec.RsaKeyGen.keySearchInit`): `e`'s value is read octet by octet,
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

namespace VG.Impl.RsaKeyGen.X86_64.KeyInit

open VG VG.X86_64

def field (j : Nat) : MemOp := { base := .rdi, disp := (8 * j : Nat) }

/-- One octet of `e` (at rdx): r9 its value so far modulo `2^32`, r10 the OR of
the bits shifted past them. -/
def octet : List Instr := [
  .movzx8 .rax { base := .rdx }, .shift .shl .r9 8, .alu .add .r9 (.reg .rax),
  .mov .rax (.reg .r9), .shift .shr .rax 32, .alu .or .r10 (.reg .rax), .mov32 .r9 (.reg .r9),
  .alu .add .rdx (.imm 1), .alu .sub .rcx (.imm 1)]

/-- `e`'s `e_len` (rcx) octets. -/
def scan : Prog isa := .seq (.block [.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .alu .test .rcx (.reg .rcx)])
  (.ite .e (.block []) (.loop (.block octet) .ne))

/-- The status in rax: 1, 2 for the size `bits` (rsi), 0 for the exponent. -/
def statusSize : List Instr := [
  .mov32 .rax (.imm 1), .mov32 .r8 (.imm 2),
  .alu .cmp .rsi (.imm 512), .cmov .b .rax (.reg .r8),
  .alu .cmp .rsi (.imm 8193), .cmov .ae .rax (.reg .r8)]

def statusExponent : List Instr := [
  .mov32 .r8 (.imm 0),
  .alu .test .r10 (.reg .r10), .cmov .ne .rax (.reg .r8),
  .mov .r11 (.reg .r9), .alu .and .r11 (.imm 1), .cmov .e .rax (.reg .r8),
  .alu .cmp .r9 (.imm 1), .cmov .e .rax (.reg .r8)]

def status : List Instr := statusSize ++ statusExponent

/-- The words: `prime_len` in rcx, the counted candidates in rdx, the budget
in rsi, the first request in r8, the generations in r10, `e`'s octets in r9. -/
def compute : List Instr := [
  .mov .rcx (.reg .rsi), .shift .shr .rcx 7, .shift .shl .rcx 3,
  .mov .rdx (.reg .rcx), .shift .shl .rdx 3, .mov .r11 (.reg .rdx), .shift .shl .rdx 2,
  .alu .add .rdx (.reg .r11), .mov .r11 (.reg .rcx), .shift .shl .r11 6,
  .alu .cmp .r9 (.imm 3), .cmov .e .rdx (.reg .r11),
  .mov .rsi (.reg .rcx), .shift .shl .rsi 15, .alu .add .rsi (.reg .rcx),
  .mov .r8 (.reg .rcx), .shift .shl .r8 5,
  .mov32 .r10 (.imm 4), .bswap .r9, .mov32 .r11 (.imm 0)]

/-- Zeros (r11) unless the status is 1. -/
def mask : List Instr := [
  .alu .cmp .rax (.imm 1),
  .cmov .ne .rcx (.reg .r11), .cmov .ne .rdx (.reg .r11), .cmov .ne .rsi (.reg .r11),
  .cmov .ne .r8 (.reg .r11), .cmov .ne .r10 (.reg .r11), .cmov .ne .r9 (.reg .r11)]

def stores : List Instr := [
  .store (field 0) .rdx, .store (field 1) .rcx, .store (field 2) .rsi, .store (field 3) .r8,
  .store (field 4) .r11, .store (field 5) .r10, .store (field 6) .r9]

def words : List Instr := compute ++ mask ++ stores

def init : Prog isa := .seq scan (.block (status ++ words))

end VG.Impl.RsaKeyGen.X86_64.KeyInit
