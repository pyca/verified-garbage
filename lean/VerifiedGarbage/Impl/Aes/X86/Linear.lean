module

public import VerifiedGarbage.Impl.Aes.X86.Sbox

/-!
# Bitsliced state in general registers, on x86 (32-bit)

The state of two AES blocks is eight 32-bit words in slots `0 … 7` of the
scratch buffer at `edi`, word `j` holding bit `j` of the 32 bytes: byte
`i = r + 4c` (row `r`, column `c`) of block `b` is at bit position
`8r + 2c + b`, as in BearSSL's `aes_ct` (Thomas Pornin, MIT licence), whose
`ortho` this follows. The key expansion (`ExpandKey.lean`) uses it, as do
other ciphers' kernels. The model has no left shift: a left shift of bits
that the mask has already cleared at the top is a rotation.

`ortho` uses the registers `tmpRegs` only, and slots `0 … 7`.
-/

@[expose] public section

namespace VG.Impl.Aes.X86

open VG.X86

def rorI (d : Reg) (n : Nat) : Instr := .shift .ror d n
def shrI (d : Reg) (n : Nat) : Instr := .shift .shr d n
def andI (d : Reg) (v : BitVec 32) : Instr := .alu .and d (.imm v)

/-! ## Between bytes and the bitsliced state -/

/-- A delta swap between slots `a` and `b` (BearSSL's `SWAPN`): exchanges the
bits of `b` in the mask `m` with the bits of `a` `s` places above them. -/
def swapN (a b : Nat) (m : BitVec 32) (s : Nat) : List Instr :=
  [movS .eax a, movS .ebx b, movR .ecx .eax, shrI .ecx s, xorR .ecx .ebx, andI .ecx m,
   xorR .ebx .ecx, rorI .ecx (32 - s), xorR .eax .ecx, st a .eax, st b .ebx]

/-- BearSSL's `br_aes_ct_ortho`: transposes the 8×8 bit matrix of each byte
position of the eight words. It is its own inverse: from two blocks (bytes
`4w … 4w + 3` of block `b` in slot `2w + b`, little-endian) to the bitsliced
state, and back. -/
def ortho : List Instr :=
  ([(0, 1), (2, 3), (4, 5), (6, 7)].flatMap fun (a, b) => swapN a b 0x55555555 1) ++
  ([(0, 2), (1, 3), (4, 6), (5, 7)].flatMap fun (a, b) => swapN a b 0x33333333 2) ++
  ([(0, 4), (1, 5), (2, 6), (3, 7)].flatMap fun (a, b) => swapN a b 0x0F0F0F0F 4)

/-- The register pointing to the round key. -/
def kp : Reg := .esi

end VG.Impl.Aes.X86
