import VerifiedGarbage.Impl.Camellia.Circuit
import VerifiedGarbage.Impl.Aes.X86.Sbox

/-!
# The bitsliced Camellia S-box on x86 (32-bit)

The circuit `Circuit.sbox` (`SBOX1`) on the eight planes in slots `0 … 7`
of the scratch buffer at `edi` (slot `j` holds bit `j` of 32 bytes: a word
of eight blocks), in place, with `eax`, `ebx`, `ecx`, `edx` and `ebp` and
spilling to slots 8–31: the code that the AES allocator `compile` produces
for it. It is written out (and `#guard` checks that it is what `compile`
produces) so that the kernel, which evaluates the code in the proofs, does
not have to run the allocator.
-/

namespace VG.Impl.Camellia.X86

open VG.X86 VG.Impl.Aes.X86

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`, in slot `7 - i`. -/
def sboxIns : List (Nat × Nat) := (List.range 8).map fun i => (VG.Impl.Camellia.Circuit.x i, 7 - i)
def sboxOuts : List (Nat × Nat) := (List.range 8).map fun i => (VG.Impl.Camellia.Circuit.s i, 7 - i)

/-- The slots the S-box may spill to. -/
def spillSlots : List Nat := List.range' 8 24

/-- `SBOX1` on the planes in slots `0 … 7`, in place. -/
def sboxCode : List Instr := [
  movS .eax 7, xorS .eax 1, movS .ebx 5, xorS .ebx 3, movS .ecx 2, xorR .ecx .eax, movS .edx 6, xorS .edx 0,
  movS .ebp 0, xorR .ebp .ebx, st 8 .eax, movS .eax 4, xorS .eax 1, st 9 .eax, movS .eax 4, xorR .eax .ecx,
  st 10 .eax, movS .eax 6, xorR .eax .ebx, st 11 .ebx, movS .ebx 2, xorR .ebx .edx, st 12 .ebx, movR .ebx .ecx,
  xorR .ebx .edx, st 13 .ebx, movS .ebx 7, xorS .ebx 6, st 14 .eax, movS .eax 7, xorR .eax .edx, notR .eax,
  st 15 .eax, movS .eax 6, xorS .eax 3, st 16 .eax, movS .eax 5, xorS .eax 1, st 17 .eax, movS .eax 5,
  xorS .eax 0, st 18 .eax, movS .eax 5, xorR .eax .ecx, xorS .edx 4, xorS .ebx 4, st 19 .edx, movS .edx 3,
  xorS .edx 0, notR .edx, st 20 .edx, movS .edx 2, xorR .edx .ebp, st 21 .eax, movS .eax 2, xorS .eax 9,
  notR .eax, st 22 .edx, movS .edx 1, xorS .edx 14, notR .edx, st 23 .edx, movS .edx 8, xorR .edx .ebp,
  st 24 .edx, movS .edx 8, xorS .edx 14, st 14 .edx, movS .edx 11, xorS .edx 9, st 8 .eax, movS .eax 11,
  xorS .eax 10, st 25 .eax, movS .eax 11, xorS .eax 13, st 11 .eax, movR .eax .ecx, xorR .eax .ebp, notR .eax,
  xorS .ecx 16, notR .ecx, xorS .ebp 9, notR .ebp, st 9 .ecx, movS .ecx 10, xorS .ecx 18, notR .ecx,
  st 18 .ebp, movS .ebp 12, xorS .ebp 17, notR .ebp, xorS .edx 12, notR .edx, st 12 .edx, movS .edx 7,
  xorS .edx 6, notR .edx, xorS .edx 6, st 17 .eax, movS .eax 7, xorS .eax 1, notR .eax, st 16 .eax,
  movS .eax 8, andR .eax .ebx, st 26 .ebx, movR .ebx .edx, andR .ebx .ebp, xorR .ebx .eax, st 27 .edx,
  movS .edx 10, andR .edx .ecx, xorR .edx .eax, movS .eax 22, andS .eax 17, st 28 .ecx, movS .ecx 14,
  andS .ecx 21, xorR .ecx .eax, st 29 .ebp, movS .ebp 13, andS .ebp 20, xorR .ebp .eax, movS .eax 19,
  andS .eax 25, st 30 .ebp, movS .ebp 18, andS .ebp 12, xorR .ebp .eax, st 31 .ecx, movS .ecx 23, andS .ecx 15,
  xorR .ecx .eax, xorR .ebx .ebp, xorR .edx .ecx, xorS .ebp 31, xorS .ecx 30, xorS .ebx 11, xorS .edx 24,
  xorS .ebp 16, xorS .ecx 9, movR .eax .ebx, xorR .eax .edx, andR .ebx .ebp, st 9 .ebp, movR .ebp .ecx,
  xorR .ebp .ebx, st 16 .ebx, movR .ebx .eax, andR .ebx .ebp, xorR .ebx .edx, st 24 .eax, movS .eax 9,
  xorR .eax .ecx, xorS .edx 16, andR .edx .eax, xorR .edx .ecx, movS .eax 9, xorR .eax .edx, st 9 .ebx,
  movR .ebx .ebp, xorR .ebx .edx, andR .ecx .ebx, xorR .eax .ecx, xorR .ebp .ecx, andS .ebp 9, xorS .ebp 24,
  movR .ecx .ebp, xorR .ecx .eax, movS .ebx 9, xorR .ebx .edx, st 24 .ebx, movS .ebx 9, xorR .ebx .ebp,
  st 16 .ebp, movR .ebp .edx, xorR .ebp .eax, st 11 .ebx, movS .ebx 24, xorR .ebx .ecx, st 30 .ecx,
  movR .ecx .ebp, andS .ecx 26, st 26 .ecx, movR .ecx .eax, andS .ecx 29, st 29 .ecx, movR .ecx .edx,
  andS .ecx 28, st 28 .ecx, movS .ecx 11, andS .ecx 17, st 17 .ecx, movS .ecx 16, andS .ecx 21, st 21 .ecx,
  movS .ecx 9, andS .ecx 20, st 20 .ecx, movS .ecx 24, andS .ecx 25, st 25 .ecx, movR .ecx .ebx, andS .ecx 12,
  st 12 .ecx, movS .ecx 30, andS .ecx 15, andS .ebp 8, andS .eax 27, andS .edx 10, st 10 .eax, movS .eax 11,
  andS .eax 22, st 22 .ebp, movS .ebp 16, andS .ebp 14, st 14 .ebp, movS .ebp 9, andS .ebp 13, st 13 .ebp,
  movS .ebp 24, andS .ebp 19, andS .ebx 18, st 18 .ebp, movS .ebp 30, andS .ebp 23, st 23 .ebp, movS .ebp 29,
  xorS .ebp 12, st 12 .eax, movS .eax 17, xorS .eax 20, st 17 .eax, movS .eax 25, xorR .eax .ecx, st 30 .ecx,
  movS .ecx 26, xorR .ecx .ebx, xorR .edx .ebp, st 19 .ebp, movS .ebp 12, xorS .ebp 17, st 24 .edx,
  movS .edx 18, xorR .edx .eax, st 9 .eax, movS .eax 28, xorS .eax 13, st 13 .eax, movS .eax 25, xorS .eax 23,
  st 25 .eax, movS .eax 30, xorS .eax 22, st 30 .eax, movS .eax 22, xorS .eax 10, st 22 .eax, movS .eax 14,
  xorR .eax .ebp, xorR .ebx .edx, st 14 .ebx, movR .ebx .ecx, xorS .ebx 24, st 16 .ebx, movS .ebx 26,
  xorS .ebx 28, st 28 .eax, movS .eax 29, xorS .eax 21, xorS .ecx 20, st 20 .ecx, movS .ecx 10, xorS .ecx 25,
  st 10 .eax, movS .eax 12, xorS .eax 24, st 24 .eax, movS .eax 18, xorS .eax 19, st 19 .ecx, movS .ecx 23,
  xorS .ecx 30, st 23 .ecx, movS .ecx 17, xorS .ecx 22, xorS .ebx 9, xorS .ebp 13, xorS .edx 22, st 22 .ebx,
  movS .ebx 13, xorS .ebx 30, xorS .eax 25, st 25 .edx, movS .edx 28, xorS .edx 14, st 30 .edx, movS .edx 28,
  xorS .edx 16, xorS .ecx 14, notR .ecx, st 14 .ecx, movS .ecx 16, xorS .ecx 19, notR .ecx, st 19 .ecx,
  movS .ecx 10, xorS .ecx 20, xorS .ebx 24, notR .ebx, xorS .edx 23, notR .edx, xorR .ebp .eax, xorS .ecx 25,
  notR .ecx, st 7 .ebp, st 6 .ecx, st 3 .ebx, st 1 .edx, movS .eax 14, st 5 .eax, movS .eax 22, st 4 .eax,
  movS .eax 19, st 2 .eax, movS .eax 30, st 0 .eax]

#guard sboxCode == compile sb VG.Impl.Camellia.Circuit.sbox sboxIns sboxOuts tmpRegs spillSlots

end VG.Impl.Camellia.X86
