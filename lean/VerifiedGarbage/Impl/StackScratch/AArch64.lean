module

public import VerifiedGarbage.TCB.AArch64.Isa

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

`withStackArgScratch bytes m c` is for a function whose scratch buffer
argument is passed on the stack, after `m` other stack arguments (its eight
argument registers all taken): it allocates a frame of `bytes` bytes and lays
out in it what `c` expects to find at and above `sp` on entry (the return
address is in `x30`, not on the stack): a copy of the `m` stack arguments,
the address of the buffer as stack argument `m`, and the buffer, at the
first 16-byte boundary after it (`bufOff m`, so `sp + 16 ⌊m / 2⌋ + 16`). It
passes them through `x16` (the frame's base) and `x17`, which no argument is
in. `bytes` is a multiple of 16 (`alloc`), so `sp` stays 16-byte aligned.
-/

@[expose] public section

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

/-- The offset from `sp` of the buffer of `withStackArgScratch`, after `m`
stack arguments and the buffer's address: `8m + 8`, rounded up to a multiple
of 16. -/
def bufOff (m : Nat) : Nat := 16 * (m / 2 + 1)

/-- `ldr x17, [sp, #(bytes + 8j)]; str x17, [x16, #8j]`: copy stack argument
`j` from the caller's frame into this one, whose base is in `x16`. -/
def copyArg (bytes j : Nat) : List Instr :=
  [.ldrSp .x17 (bytes + 8 * j), .str .x .x17 .x16 (8 * j)]

/-- Copy the `m` stack arguments to the frame's base (in `x16`), and pass the
buffer, at `sp + bufOff m`, as the next one. -/
def setArgs (bytes m : Nat) : List Instr :=
  .addSp .x16 0 :: (List.range m).flatMap (copyArg bytes) ++
    [.addSp .x17 (bufOff m), .str .x .x17 .x16 (8 * m)]

/-- `c`, whose scratch buffer is passed on the stack after `m` other stack
arguments, with the buffer in a frame of `bytes` bytes on the stack. -/
def withStackArgScratch (bytes m : Nat) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (setArgs bytes m)) c) (.free bytes)

end VG.Impl.StackScratch.AArch64
