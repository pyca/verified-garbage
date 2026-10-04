import VerifiedGarbage.TCB.AArch64.Isa

/-!
# A scratch buffer on the stack (AArch64)

`withStackScratch bytes r c` runs code `c`, written for a function whose last
argument is a scratch buffer, passed in `r`, without that argument: it
allocates a frame of `bytes` bytes on the stack and passes its address in
`r`. The buffer is below the stack pointer on entry, where no Rust object
lies.

`withStackScratchWiped bytes r words c` is the same, but zeroes the first
`words` doublewords of the buffer after its code (`wipe`), for a function
whose working space may hold secrets that its caller would otherwise wipe.
-/

namespace VG.Impl.StackScratch.AArch64

open VG.AArch64

/-- `c`, with its scratch buffer (passed in `r`) in a frame of `bytes` bytes
on the stack, at `sp`. -/
def withStackScratch (bytes : Nat) (r : Reg) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block [.addSp r 0]) c) (.free bytes)

/-- `str x17, [x16, #8k]` for each `k < words`. -/
def wipeStores (words : Nat) : List Instr :=
  (List.range words).map fun k => .str .x .x17 .x16 (8 * k)

/-- Zeroes the `words` doublewords at `sp`, through `x16` (their address) and
`x17` (zero). -/
def wipe (words : Nat) : List Instr := .addSp .x16 0 :: .movz .x .x17 0 0 :: wipeStores words

/-- `withStackScratch`, zeroing the first `words` doublewords of the buffer
after the code. -/
def withStackScratchWiped (bytes : Nat) (r : Reg) (words : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes r (.seq c (.block (wipe words)))

end VG.Impl.StackScratch.AArch64
