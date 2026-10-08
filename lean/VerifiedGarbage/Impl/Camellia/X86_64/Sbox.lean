import VerifiedGarbage.Impl.Camellia.Circuit
import VerifiedGarbage.Impl.Aes.X86_64.Sbox

/-!
# The bitsliced Camellia S-box on x86-64

The circuit `Circuit.sbox` (`SBOX1`) on the eight words of the bitsliced
state (`q j` holds bit `j` of 64 bytes), in place, spilling to slots 1–47
of the scratch buffer at `r9` (slot 0 holds all ones): the code that the
AES allocator `compile` produces for it, with the temporaries `r14` and
`r15`. It is written out (and `#guard` checks that it is what `compile`
produces) so that the kernel, which evaluates the code in the proofs, does
not have to run the allocator.
-/

namespace VG.Impl.Camellia.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`, in `q (7 - i)`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Camellia.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Camellia.Circuit.s i, q (7 - i))

/-- `SBOX1` on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  ones .r14, st 0 .r14, movR .r14 .r13, xorR .r14 .rbx, movR .r15 .r11, xorR .r15 .rbp,
  st 1 .r11, movR .r11 .rcx, xorR .r11 .r14, st 2 .r14, movR .r14 .r12, xorR .r14 .rax,
  st 3 .rbp, movR .rbp .rax, xorR .rbp .r15, st 4 .rbp, movR .rbp .r10, xorR .rbp .rbx,
  st 5 .rbp, movR .rbp .r10, xorR .rbp .r11, st 6 .rbp, movR .rbp .r12, xorR .rbp .r15,
  st 7 .r15, movR .r15 .rcx, xorR .r15 .r14, st 8 .r15, movR .r15 .r11, xorR .r15 .r14,
  st 9 .r15, movR .r15 .r13, xorR .r15 .r12, st 10 .rbp, movR .rbp .r13, xorR .rbp .r14,
  xorS .rbp 0, st 11 .rbp, movR .rbp .r12, xorS .rbp 3, st 12 .r13, movS .r13 1,
  xorR .r13 .rbx, st 13 .r12, movS .r12 1, xorR .r12 .rax, st 14 .r13, movS .r13 1,
  xorR .r13 .r11, xorR .r14 .r10, xorR .r10 .r15, xorS .rax 3, xorS .rax 0, movR .r15 .rcx,
  xorS .r15 4, xorS .rcx 5, xorS .rcx 0, st 3 .r14, movR .r14 .rbx, xorS .r14 10,
  xorS .r14 0, st 1 .r14, movS .r14 2, xorS .r14 4, st 15 .r14, movS .r14 2,
  xorS .r14 10, st 10 .rax, movS .rax 7, xorS .rax 5, st 2 .r14, movS .r14 7,
  xorS .r14 6, st 16 .r14, movS .r14 7, xorS .r14 9, st 7 .r14, movR .r14 .r11,
  xorS .r14 4, xorS .r14 0, xorR .r11 .rbp, xorS .r11 0, movS .rbp 4, xorS .rbp 5,
  xorS .rbp 0, xorS .r12 6, xorS .r12 0, st 5 .r11, movS .r11 8, xorS .r11 14,
  xorS .r11 0, xorS .rax 8, xorS .rax 0, st 8 .rax, movS .rax 12, xorS .rax 13,
  xorS .rax 0, xorS .rax 13, xorS .rbx 12, xorS .rbx 0, st 12 .rbx, movR .rbx .rcx,
  andR .rbx .r10, st 13 .rcx, movR .rcx .rax, andR .rcx .r11, xorR .rcx .rbx, st 14 .rax,
  movS .rax 6, andR .rax .r12, xorR .rax .rbx, movR .rbx .r15, andR .rbx .r14, st 4 .r15,
  movS .r15 2, andR .r15 .r13, xorR .r15 .rbx, st 17 .r13, movS .r13 9, andS .r13 10,
  xorR .r13 .rbx, movS .rbx 3, andS .rbx 16, st 18 .r14, movR .r14 .rbp, andS .r14 8,
  xorR .r14 .rbx, st 19 .rbp, movS .rbp 1, andS .rbp 11, xorR .rbp .rbx, xorR .rcx .r14,
  xorR .rax .rbp, xorR .r15 .r14, xorR .r13 .rbp, xorS .rcx 7, xorS .rax 15, xorS .r15 12,
  xorS .r13 5, movR .rbp .rcx, xorR .rbp .rax, andR .rcx .r15, movR .r14 .r13, xorR .r14 .rcx,
  movR .rbx .rbp, andR .rbx .r14, xorR .rbx .rax, st 5 .r12, movR .r12 .r15, xorR .r12 .r13,
  xorR .rax .rcx, andR .rax .r12, xorR .rax .r13, xorR .r15 .rax, movR .r12 .r14, xorR .r12 .rax,
  andR .r13 .r12, xorR .r15 .r13, xorR .r14 .r13, andR .r14 .rbx, xorR .rbp .r14, movR .r14 .rbp,
  xorR .r14 .r15, movR .r13 .rbx, xorR .r13 .rax, movR .r12 .rbx, xorR .r12 .rbp, movR .rcx .rax,
  xorR .rcx .r15, st 12 .rbx, movR .rbx .r13, xorR .rbx .r14, andR .r10 .rcx, andR .r11 .r15,
  st 15 .r10, movR .r10 .rax, andS .r10 5, st 5 .r10, movR .r10 .r12, andS .r10 18,
  st 18 .r10, movR .r10 .rbp, andS .r10 17, st 17 .r10, movS .r10 12, andS .r10 10,
  st 10 .r10, movR .r10 .r13, andS .r10 16, st 16 .r10, movR .r10 .rbx, andS .r10 8,
  st 8 .r10, movR .r10 .r14, andS .r10 11, andS .rcx 13, andS .r15 14, andS .rax 6,
  andS .r12 4, andS .rbp 2, st 2 .rbp, movS .rbp 12, andS .rbp 9, andS .r13 3,
  andS .rbx 19, andS .r14 1, st 1 .r15, movR .r15 .r11, xorS .r15 8, st 8 .r11,
  movS .r11 18, xorS .r11 10, st 18 .rcx, movS .rcx 16, xorR .rcx .r10, st 19 .r10,
  movS .r10 15, xorR .r10 .rbx, xorR .rax .r15, st 3 .r15, movR .r15 .r12, xorR .r15 .r11,
  st 9 .r11, movR .r11 .r13, xorR .r11 .rcx, xorS .rbp 5, st 12 .rbp, movS .rbp 16,
  xorR .rbp .r14, st 16 .rcx, movS .rcx 19, xorS .rcx 18, st 19 .rcx, movS .rcx 18,
  xorS .rcx 1, st 18 .rcx, movS .rcx 2, xorR .rcx .r15, xorR .rbx .r11, st 2 .rbx,
  movR .rbx .r10, xorR .rbx .rax, st 4 .rbx, movS .rbx 15, xorS .rbx 5, st 5 .rcx,
  movS .rcx 8, xorS .rcx 17, xorS .r10 10, st 10 .r10, movS .r10 1, xorR .r10 .rbp,
  xorR .r12 .rax, xorS .r13 3, xorS .r14 19, movS .rax 9, xorS .rax 18, xorS .rbx 16,
  xorS .r15 12, xorS .r11 18, st 18 .rbx, movS .rbx 12, xorS .rbx 19, xorR .rbp .r13,
  movS .r13 5, xorS .r13 2, st 19 .r13, movS .r13 5, xorS .r13 4, xorS .rax 2,
  xorS .rax 0, xorS .r10 4, xorS .r10 0, xorS .rcx 10, xorR .r12 .rbx, xorS .r12 0,
  xorR .r14 .r13, xorS .r14 0, xorR .r15 .rbp, xorR .r11 .rcx, xorS .r11 0, movR .r13 .r15,
  st 10 .r12, movR .r12 .r11, movR .r11 .rax, st 4 .r10, movS .r10 18, movS .rbp 10,
  movS .rcx 4, movR .rbx .r14, movS .rax 19]

#guard sboxCode == compile sb VG.Impl.Camellia.Circuit.sbox sboxIns sboxOuts [t0, t1] onesSlot spillSlots

end VG.Impl.Camellia.X86_64
