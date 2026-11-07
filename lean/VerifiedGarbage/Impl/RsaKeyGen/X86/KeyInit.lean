module

public import VerifiedGarbage.Impl.Bignum.X86.PublicRt

/-! # Starting RSA key generation on i686

`vg_rsa_generate_init(state, bits, e, e_len)`
(`VG.Spec.RsaKeyGen.keySearchInit`), as on x86-64
(`Impl/RsaKeyGen/X86_64/KeyInit.lean`): `e`'s value is read octet by octet,
keeping its low 32 bits and whether any bit above them is set; the status is
1, 2 for a size above 8192 bits or below 512 rounded down to a multiple of
128, or 0 (which overrides 2) for an exponent that is above 32 bits, even, or
1. The words are the first prime's counted candidates (`40 prime_len`, or
`64 prime_len` for `e = 3`), the primes' octets `prime_len = 8 (bits / 128)`,
the budget `32769 prime_len`, the first request `32 prime_len`, the phase 0,
the four generations and `e`'s eight octets, most significant first; or seven
zeros. Each `u64` word is two 32-bit stores, its high half zero.

The contract leaves no stack, so, as `vg_rsa_prime_search_init` does
(`Impl/RsaKeyGen/X86/SearchInit.lean`), the caller's `ebx` is saved in the
state's first word and `ebx` holds the state's pointer; the value of `e`, the
OR of the bits shifted past it, and the masks are kept in the state's words 4
and 5 (bytes 32 to 47) until the words are written. Only the loop over `e`'s
octets branches, on `e_len`; the status and the masks come from the borrows of
comparisons.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86.KeyInit

open VG VG.X86
open VG.Impl.Mont.X86 (at_)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- Argument `i` (`state, bits, e, e_len`). -/
def param (i : Nat) : MemOp := argAt 0 i

/-- The state's bytes from `d`, at `ebx`. -/
def sb (d : Nat) : MemOp := at_ .ebx d

/-- `ebx` saved in the first word, then the state's pointer; the value and
the bits past it zero. -/
def enter : List Instr :=
  [.mov .edx (.mem (param 0)), .store (at_ .edx 0) .ebx, .mov .ebx (.reg .edx), .mov .eax (.imm 0),
    .store (sb 32) .eax, .store (sb 36) .eax]

/-- One octet of `e` (at `ecx`, kept in bytes 44): the value (bytes 32) times
256 plus the octet, modulo `2 ^ 32`, and the octet shifted past it ORed into
bytes 36. -/
def octet : List Instr :=
  [.movzx8 .eax (at_ .ecx 0), .store (sb 44) .eax,
    .mov .eax (.mem (sb 32)), .shift .shr .eax 24, .alu .or .eax (.mem (sb 36)), .store (sb 36) .eax,
    .mov .eax (.mem (sb 32))] ++ List.replicate 8 (.alu .add .eax (.reg .eax)) ++
  [.alu .add .eax (.mem (sb 44)), .store (sb 32) .eax,
    .alu .add .ecx (.imm 1), .alu .sub .edx (.imm 1)]

/-- `e`'s `e_len` octets. -/
def scan : Prog isa :=
  .seq (.block [.mov .ecx (.mem (param 2)), .mov .edx (.mem (param 3)), .alu .cmp .edx (.imm 0)])
    (.ite .e (.block []) (.loop (.block octet) .ne))

/-- The masks and the status: `ecx` all ones for an exponent that is above 32
bits, even or below 3 (bytes 40), the mask of `e = 3` (bytes 36), then `ecx`
all ones for a size out of range; the status (bytes 44) and the mask of a
valid start (bytes 40). -/
def status : List Instr :=
  [.mov .eax (.mem (sb 36)), .alu .cmp .eax (.imm 1), .alu .sbb .ecx (.reg .ecx),
    .alu .xor .ecx (.imm 0xffffffff),
    .mov .edx (.mem (sb 32)), .mov .eax (.reg .edx), .alu .and .eax (.imm 1), .alu .cmp .eax (.imm 1),
    .alu .sbb .eax (.reg .eax), .alu .or .ecx (.reg .eax),
    .alu .cmp .edx (.imm 3), .alu .sbb .eax (.reg .eax), .alu .or .ecx (.reg .eax),
    .store (sb 40) .ecx,
    .mov .eax (.reg .edx), .alu .xor .eax (.imm 3), .alu .cmp .eax (.imm 1), .alu .sbb .eax (.reg .eax),
    .store (sb 36) .eax,
    .mov .eax (.mem (param 1)), .alu .cmp .eax (.imm 512), .alu .sbb .ecx (.reg .ecx),
    .alu .cmp .eax (.imm 8193), .alu .sbb .edx (.reg .edx), .alu .xor .edx (.imm 0xffffffff),
    .alu .or .ecx (.reg .edx),
    .mov .eax (.reg .ecx), .alu .and .eax (.imm 1), .alu .add .eax (.imm 1), .mov .edx (.mem (sb 40)),
    .alu .xor .edx (.imm 0xffffffff), .alu .and .eax (.reg .edx), .store (sb 44) .eax,
    .alu .or .ecx (.mem (sb 40)), .alu .xor .ecx (.imm 0xffffffff), .store (sb 40) .ecx]

/-- The words, masked: `prime_len` (`ecx`), the high halves and the high half
of `e`'s word zero, the budget, the first request, the counted candidates,
`e`'s octets, the generations and the phase; the status returned, `ebx`
restored and the first word written. -/
def words : List Instr :=
  [.mov .ecx (.mem (param 1)), .shift .shr .ecx 7, .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    .alu .add .ecx (.reg .ecx), .alu .and .ecx (.mem (sb 40)), .store (sb 8) .ecx,
    .mov .eax (.imm 0), .store (sb 4) .eax, .store (sb 12) .eax, .store (sb 20) .eax, .store (sb 28) .eax,
    .store (sb 48) .eax,
    .mov .eax (.imm 32769), .mul .ecx, .store (sb 16) .eax,
    .mov .eax (.reg .ecx), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .store (sb 24) .eax,
    .mov .eax (.reg .ecx), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .mov .edx (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .edx), .alu .and .eax (.mem (sb 36)),
    .store (sb 36) .eax,
    .mov .eax (.imm 40), .mul .ecx, .alu .add .eax (.mem (sb 36)), .mov .ecx (.reg .eax),
    .mov .eax (.mem (sb 32)), .alu .and .eax (.mem (sb 40)), .bswap .eax, .store (sb 52) .eax,
    .mov .eax (.imm 4), .alu .and .eax (.mem (sb 40)), .store (sb 40) .eax,
    .mov .eax (.imm 0), .store (sb 32) .eax, .store (sb 36) .eax,
    .mov .eax (.mem (sb 44)), .mov .edx (.imm 0), .store (sb 44) .edx,
    .mov .edx (.mem (param 0)), .mov .ebx (.mem (at_ .edx 0)), .store (at_ .edx 0) .ecx]

def init : Prog isa := .seq (.block enter) (.seq scan (.block (status ++ words)))

end VG.Impl.RsaKeyGen.X86.KeyInit
