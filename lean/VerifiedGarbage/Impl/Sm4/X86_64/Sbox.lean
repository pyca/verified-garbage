module

public import VerifiedGarbage.Impl.Sm4.Circuit
meta import VerifiedGarbage.Impl.Sm4.Circuit
public import VerifiedGarbage.Impl.Aes.X86_64.Sbox
meta import VerifiedGarbage.Impl.Aes.X86_64.Sbox

/-!
# The bitsliced SM4 S-box on x86-64

The circuit `Circuit.sbox` on the eight words of the bitsliced state
(`q j` holds bit `j` of 64 bytes), in place, spilling to slots 1–47
of the scratch buffer at `r9` (slot 0 holds all ones): the code that the
AES allocator `compile` produces for it, with the temporaries `r14` and
`r15`. It is written out (and `#guard` checks that it is what `compile`
produces) so that the kernel, which evaluates the code in the proofs, does
not have to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`, in `q (7 - i)`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Sm4.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Sm4.Circuit.s i, q (7 - i))

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  ones .r14, st 0 .r14, movR .r14 .r10, xorR .r14 .rcx, movR .r15 .rbp, xorR .r15 .rax, st 1 .rax,
  movR .rax .rbx, xorR .rax .r15, st 2 .r15, movR .r15 .r13, xorR .r15 .r14, st 3 .rbx,
  movR .rbx .r11, xorR .rbx .rax, st 4 .rax, movR .rax .r12, xorR .rax .rcx, xorR .r10 .r13,
  st 5 .rcx, movR .rcx .r11, xorR .rcx .r15, st 6 .rax, movR .rax .r12, xorR .rax .rcx, st 7 .rax,
  movR .rax .r13, xorR .rax .rbp, st 8 .r13, movR .r13 .r12, xorR .r13 .r10, st 9 .r10,
  movR .r10 .r11, xorR .r10 .r14, xorS .rcx 3, xorS .rcx 0, st 10 .rcx, movS .rcx 2,
  xorR .rcx .r15, st 11 .r11, movS .r11 1, xorR .r11 .r13, xorR .r13 .rbx, st 12 .r13, movS .r13 3,
  xorS .r13 6, xorR .r12 .rcx, movS .rcx 1, xorR .rcx .r15, xorS .rcx 0, st 1 .r15, movS .r15 3,
  xorR .r15 .rax, xorR .rbp .r10, xorS .rbp 0, st 13 .rcx, movS .rcx 4, xorS .rcx 9, st 9 .rcx,
  movR .rcx .r14, xorR .rcx .rbx, st 14 .rcx, movR .rcx .rbx, xorS .rcx 6, st 15 .rcx, movS .rcx 8,
  xorS .rcx 5, xorS .rcx 0, xorS .r11 3, xorS .r11 0, xorS .r10 2, xorS .rax 11, xorS .rax 0,
  st 11 .r11, movS .r11 3, xorS .r11 7, xorS .r14 4, xorS .r14 0, st 2 .rcx, movS .rcx 8,
  xorS .rcx 4, xorS .rcx 0, st 4 .rcx, movR .rcx .r11, andS .rcx 10, st 8 .r11, movR .r11 .rbx,
  andR .r11 .rbp, xorR .r11 .rcx, st 5 .rbx, movR .rbx .r12, andR .rbx .r15, xorR .rbx .rcx,
  movS .rcx 3, andR .rcx .r10, st 16 .r12, movS .r12 6, andR .r12 .rax, xorR .r12 .rcx, st 17 .rax,
  movR .rax .r13, andS .rax 13, xorR .rax .rcx, movS .rcx 9, andR .rcx .r14, st 18 .r13,
  movS .r13 7, andS .r13 4, xorR .r13 .rcx, st 19 .r14, movS .r14 15, andS .r14 1, xorR .r14 .rcx,
  xorR .r11 .r13, xorR .rbx .r14, xorR .r12 .r13, xorR .rax .r14, xorS .r11 2, xorS .rbx 12,
  xorS .r12 14, xorS .rax 11, movR .r14 .r11, xorR .r14 .rbx, andR .r11 .r12, movR .r13 .rax,
  xorR .r13 .r11, movR .rcx .r14, andR .rcx .r13, xorR .rcx .rbx, st 11 .r10, movR .r10 .r12,
  xorR .r10 .rax, xorR .rbx .r11, andR .rbx .r10, xorR .rbx .rax, xorR .r12 .rbx, movR .r10 .r13,
  xorR .r10 .rbx, andR .rax .r10, xorR .r12 .rax, xorR .r13 .rax, andR .r13 .rcx, xorR .r14 .r13,
  movR .r13 .r14, xorR .r13 .r12, movR .rax .rcx, xorR .rax .rbx, movR .r10 .rcx, xorR .r10 .r14,
  movR .r11 .rbx, xorR .r11 .r12, st 14 .rcx, movR .rcx .rax, xorR .rcx .r13, st 12 .r13,
  movR .r13 .r11, andS .r13 10, andR .rbp .r12, andR .r15 .rbx, st 10 .r15, movR .r15 .r10,
  andS .r15 11, st 11 .r15, movR .r15 .r14, andS .r15 17, st 17 .r15, movS .r15 14, andS .r15 13,
  st 13 .rbp, movR .rbp .rax, andS .rbp 19, st 19 .r15, movR .r15 .rcx, andS .r15 4, st 4 .r15,
  movS .r15 12, andS .r15 1, andS .r11 8, andS .r12 5, andS .rbx 16, andS .r10 3, andS .r14 6,
  st 6 .r10, movS .r10 14, andS .r10 18, andS .rax 9, andS .rcx 7, st 7 .rcx, movS .rcx 12,
  andS .rcx 15, xorR .r11 .rax, xorR .rbp .r12, st 15 .r12, movR .r12 .r13, xorS .r12 19,
  st 19 .r13, movR .r13 .r14, xorR .r13 .rbp, xorR .r10 .r13, xorS .r15 13, movS .r13 4,
  xorR .r13 .r10, xorR .rcx .r11, st 12 .r10, movS .r10 17, xorR .r10 .r12, st 9 .rbp,
  movR .rbp .r13, xorR .rbp .rcx, st 18 .rbp, movR .rbp .rbx, xorR .rbp .r10, st 14 .r13,
  movS .r13 7, xorR .r13 .r15, xorR .r11 .r13, xorS .r12 11, xorR .r12 .r11, xorR .rbx .rcx,
  xorS .r14 7, xorS .rax 6, xorS .r10 9, xorR .r15 .rbp, xorS .r15 12, xorS .r15 0, xorS .r12 15,
  movS .rcx 10, xorS .rcx 14, xorS .r12 4, xorS .r12 0, xorR .r14 .rax, xorS .r14 0, movS .rax 19,
  xorS .rax 13, movS .r13 11, xorS .r13 18, xorS .rax 18, xorR .rbp .rcx, xorS .rbp 0,
  xorS .r13 17, xorR .r11 .r10, xorS .r11 0, st 17 .r13, movR .r13 .r14, st 18 .r12,
  movR .r12 .rbp, st 11 .r11, movR .r11 .rax, movS .r10 11, movR .rbp .rbx, movS .rcx 17,
  movR .rbx .r15, movS .rax 18]

#guard sboxCode == compile sb VG.Impl.Sm4.Circuit.sbox sboxIns sboxOuts [t0, t1] onesSlot spillSlots

end VG.Impl.Sm4.X86_64
