import VerifiedGarbage.Impl.Sm4.Circuit
import VerifiedGarbage.Impl.Aes.X86.Sbox

/-!
# The bitsliced SM4 S-box on x86 (32-bit)

The circuit `Circuit.sbox` on the eight planes of a word of eight blocks
(slot `j` of the scratch buffer at `edi` holds bit `j` of 32 bytes), in
place, with `eax`, `ebx`, `ecx`, `edx` and `ebp` and spilling to slots
8–31: the code that the AES allocator `compile` produces for it. It is
written out (and `#guard` checks that it is what `compile` produces) so
that the kernel, which evaluates the code in the proofs, does not have to
run the allocator.
-/

namespace VG.Impl.Sm4.X86

open VG.X86 VG.Impl.Aes.X86

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`, in slot `7 - i`. -/
def sboxIns : List (Nat × Nat) := (List.range 8).map fun i => (VG.Impl.Sm4.Circuit.x i, 7 - i)
def sboxOuts : List (Nat × Nat) := (List.range 8).map fun i => (VG.Impl.Sm4.Circuit.s i, 7 - i)

/-- The slots the S-box may spill to. -/
def spillSlots : List Nat := List.range' 8 24

/-- The S-box on the planes in slots `0 … 7`, in place. -/
def sboxCode : List Instr := [
  movS .eax 4, xorS .eax 2, movS .ebx 3, xorS .ebx 0, movS .ecx 1, xorR .ecx .ebx, movS .edx 7,
  xorR .edx .eax, movS .ebp 5, xorR .ebp .ecx, st 8 .ecx, movS .ecx 6, xorS .ecx 2, st 9 .ecx, movS .ecx 7,
  xorS .ecx 4, st 10 .ebp, movS .ebp 5, xorR .ebp .edx, st 11 .edx, movS .edx 6, xorR .edx .ebp, st 12 .edx,
  movS .edx 7, xorS .edx 3, st 13 .edx, movS .edx 6, xorR .edx .ecx, st 14 .ecx, movS .ecx 5, xorR .ecx .eax,
  xorS .ebp 1, notR .ebp, st 15 .ebp, movR .ebp .ebx, xorS .ebp 11, st 16 .ebx, movS .ebx 0, xorR .ebx .edx,
  xorS .edx 10, st 17 .edx, movS .edx 1, xorS .edx 9, xorS .ebp 6, st 18 .edx, movS .edx 0, xorS .edx 11,
  notR .edx, st 19 .edx, movS .edx 1, xorS .edx 13, st 20 .edx, movS .edx 3, xorR .edx .ecx, notR .edx,
  st 21 .ebp, movS .ebp 8, xorS .ebp 14, st 14 .ebp, movR .ebp .eax, xorS .ebp 10, st 22 .ebp, movS .ebp 10,
  xorS .ebp 9, st 23 .ebp, movS .ebp 7, xorS .ebp 2, notR .ebp, xorS .ebx 1, notR .ebx, xorS .ecx 16,
  st 16 .ebx, movS .ebx 5, xorS .ebx 13, notR .ebx, st 13 .ebp, movS .ebp 1, xorS .ebp 12, xorS .eax 8,
  notR .eax, st 24 .eax, movS .eax 7, xorS .eax 8, notR .eax, st 8 .eax, movR .eax .ebp, andS .eax 15,
  st 25 .ebp, movS .ebp 10, andR .ebp .edx, xorR .ebp .eax, st 26 .edx, movS .edx 21, andS .edx 20,
  xorR .edx .eax, movS .eax 1, andR .eax .ecx, st 27 .ecx, movS .ecx 9, andR .ecx .ebx, xorR .ecx .eax,
  st 28 .ebx, movS .ebx 18, andS .ebx 19, xorR .ebx .eax, movS .eax 14, andS .eax 24, st 29 .ebx,
  movS .ebx 12, andS .ebx 8, xorR .ebx .eax, st 30 .ecx, movS .ecx 23, andS .ecx 11, xorR .ecx .eax,
  xorR .ebp .ebx, xorR .edx .ecx, xorS .ebx 30, xorS .ecx 29, xorS .ebp 13, xorS .edx 17, xorS .ebx 22,
  xorS .ecx 16, movR .eax .ebp, xorR .eax .edx, andR .ebp .ebx, st 16 .ebx, movR .ebx .ecx, xorR .ebx .ebp,
  st 22 .ebp, movR .ebp .eax, andR .ebp .ebx, xorR .ebp .edx, st 17 .eax, movS .eax 16, xorR .eax .ecx,
  xorS .edx 22, andR .edx .eax, xorR .edx .ecx, movS .eax 16, xorR .eax .edx, st 16 .ebp, movR .ebp .ebx,
  xorR .ebp .edx, andR .ecx .ebp, xorR .eax .ecx, xorR .ebx .ecx, andS .ebx 16, xorS .ebx 17, movR .ecx .ebx,
  xorR .ecx .eax, movS .ebp 16, xorR .ebp .edx, st 17 .ebp, movS .ebp 16, xorR .ebp .ebx, st 22 .ebx,
  movR .ebx .edx, xorR .ebx .eax, st 13 .ebp, movS .ebp 17, xorR .ebp .ecx, st 29 .ecx, movR .ecx .ebx,
  andS .ecx 15, st 15 .ecx, movR .ecx .eax, andS .ecx 26, st 26 .ecx, movR .ecx .edx, andS .ecx 20,
  st 20 .ecx, movS .ecx 13, andS .ecx 27, st 27 .ecx, movS .ecx 22, andS .ecx 28, st 28 .ecx, movS .ecx 16,
  andS .ecx 19, st 19 .ecx, movS .ecx 17, andS .ecx 24, st 24 .ecx, movR .ecx .ebp, andS .ecx 8, st 8 .ecx,
  movS .ecx 29, andS .ecx 11, andS .ebx 25, andS .eax 10, andS .edx 21, st 21 .edx, movS .edx 13,
  andS .edx 1, st 13 .edx, movS .edx 22, andS .edx 9, st 9 .ecx, movS .ecx 16, andS .ecx 18, st 18 .ecx,
  movS .ecx 17, andS .ecx 14, andS .ebp 12, st 12 .ebp, movS .ebp 29, andS .ebp 23, xorR .ebx .ecx,
  st 23 .ecx, movS .ecx 24, xorR .ecx .eax, st 24 .eax, movS .eax 15, xorS .eax 19, st 19 .eax,
  movR .eax .edx, xorR .eax .ecx, xorS .eax 18, st 18 .ecx, movS .ecx 26, xorS .ecx 9, st 9 .edx,
  movS .edx 8, xorR .edx .eax, xorR .ebp .ebx, st 29 .eax, movS .eax 28, xorS .eax 19, st 14 .ebx,
  movR .ebx .edx, xorR .ebx .ebp, st 17 .ebx, movS .ebx 21, xorR .ebx .eax, st 16 .edx, movS .edx 12,
  xorR .edx .ecx, xorS .edx 14, st 14 .ebx, movS .ebx 27, xorS .ebx 19, xorR .ebx .edx, xorS .ebp 21,
  st 21 .ebp, movS .ebp 9, xorS .ebp 12, st 12 .edx, movS .edx 13, xorS .edx 23, xorS .eax 18, xorS .ecx 14,
  xorS .ecx 29, notR .ecx, xorS .ebx 24, st 24 .ecx, movS .ecx 20, xorS .ecx 16, xorS .ebx 8, notR .ebx,
  xorR .ebp .edx, notR .ebp, movS .edx 15, xorS .edx 26, st 26 .ebp, movS .ebp 27, xorS .ebp 17,
  xorS .edx 17, xorS .ecx 14, notR .ecx, xorS .ebp 28, xorS .eax 12, notR .eax, st 6 .ecx, st 5 .edx,
  st 4 .eax, st 2 .ebp, st 0 .ebx, movS .eax 26, st 7 .eax, movS .eax 21, st 3 .eax, movS .eax 24, st 1 .eax]

#guard sboxCode == compile sb VG.Impl.Sm4.Circuit.sbox sboxIns sboxOuts tmpRegs spillSlots

end VG.Impl.Sm4.X86
