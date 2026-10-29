module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# A scratch buffer on the stack (RISC-V)

`withStackScratch bytes r c` runs code `c`, written for a function whose last
argument is a scratch buffer, passed in `r`, without that argument: it
allocates a frame of `bytes` bytes on the stack (`addi sp, sp, -bytes`) and
passes its address, `sp`, in `r`. The buffer is below the stack pointer on
entry, where no Rust object lies.

`withStackScratchWiped bytes r words c` is the same, but zeroes the first
`words` doublewords of the buffer after its code (`wipe`), for a function
whose working space may hold secrets that its caller would otherwise wipe.
A store's offset reaches 2047 bytes, so beyond 256 doublewords the wipe
stores the first 255 from `sp` and the rest from `sp + 2040`.
-/

@[expose] public section

namespace VG.Impl.StackScratch.RISCV64

open VG.RISCV64

/-- `c`, with its scratch buffer (passed in `r`) in a frame of `bytes` bytes
on the stack, at `sp`. -/
def withStackScratch (bytes : Nat) (r : Reg) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block [.addSp r 0]) c) (.free bytes)

/-- `sd t6, 8k(t5)` for each `k < words`. -/
def wipeStores (words : Nat) : List Instr :=
  (List.range words).map fun k => .store .d .t6 .t5 (8 * k)

/-- The stores of `wipe`: from `t5` alone up to 256 doublewords, else the
first 255 from `t5` and the rest from `t5 + 2040`. -/
def wipeAll (words : Nat) : List Instr :=
  if words ≤ 256 then wipeStores words
  else wipeStores 255 ++ .addi .t5 .t5 2040 :: wipeStores (words - 255)

/-- Zeroes the `words` doublewords of the buffer, at `sp`, through `t5`
(their address) and `t6` (zero). -/
def wipe (words : Nat) : List Instr := .addSp .t5 0 :: .li .t6 0 :: wipeAll words

/-- `withStackScratch`, zeroing the first `words` doublewords of the buffer
after the code. -/
def withStackScratchWiped (bytes : Nat) (r : Reg) (words : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes r (.seq c (.block (wipe words)))

end VG.Impl.StackScratch.RISCV64
