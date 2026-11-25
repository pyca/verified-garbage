module

public import VerifiedGarbage.Impl.Aes.X86.Sbox

/-!
# Bytes and bit slices on x86 (32-bit), in general registers

Immediate forms of instructions, and the transpose of the four 8×8 bit
matrices that the words in slots `0 … 7` hold, a byte of each (`ortho`, its
own inverse: bit `j` of byte `p` of slot `k` becomes bit `k` of byte `p` of
slot `j`).

Number the bits of a word, and the words, in binary. The transpose exchanges
three bits of the number of the bit with the three of the number of the
word, one after the other: each time, four pairs of words exchange the half
of their bits that have the one bit set in the one word and clear in the
other (`exchange`). The pairs that differ in the low bit of the word's
number, or the next, are within a group of four words, so those two passes
are done for each group in registers (`orthoGroup`), and then the last.
-/

@[expose] public section

namespace VG.Impl.Aes.X86

open VG.X86

def rorI (d : Reg) (n : Nat) : Instr := .shift .ror d n
def shrI (d : Reg) (n : Nat) : Instr := .shift .shr d n
def andI (d : Reg) (v : BitVec 32) : Instr := .alu .and d (.imm v)

/-- The bits of `lo` that are `n` above a position of `m` exchanged with the
bits of `hi` at those positions, through `t`. What is rotated left by `n` is
masked, so that it does not wrap around. -/
def exchange (lo hi t : Reg) (n : Nat) (m : BitVec 32) : List Instr :=
  [movR t lo, shrI t n, xorR t hi, andI t m, xorR hi t, rorI t (32 - n), xorR lo t]

/-- The masks of the positions whose number has a bit clear, by its place. -/
def mask1 : BitVec 32 := 0x55555555
def mask2 : BitVec 32 := 0x33333333
def mask4 : BitVec 32 := 0x0F0F0F0F

/-- Words `4 g … 4 g + 3`: the two low bits of the numbers. -/
def orthoGroup (g : Nat) : List Instr :=
  [movS .eax (4 * g), movS .ebx (4 * g + 1), movS .ecx (4 * g + 2), movS .edx (4 * g + 3)] ++
  exchange .eax .ebx .ebp 1 mask1 ++ exchange .ecx .edx .ebp 1 mask1 ++
  exchange .eax .ecx .ebp 2 mask2 ++ exchange .ebx .edx .ebp 2 mask2 ++
  [st (4 * g) .eax, st (4 * g + 1) .ebx, st (4 * g + 2) .ecx, st (4 * g + 3) .edx]

/-- Words `k` and `k + 4`: the third bit. -/
def orthoPair (k : Nat) : List Instr :=
  [movS .eax k, movS .ebx (k + 4)] ++ exchange .eax .ebx .ebp 4 mask4 ++ [st k .eax, st (k + 4) .ebx]

/-- The transpose. -/
def ortho : List Instr := orthoGroup 0 ++ orthoGroup 1 ++ (List.range 4).flatMap orthoPair

end VG.Impl.Aes.X86
