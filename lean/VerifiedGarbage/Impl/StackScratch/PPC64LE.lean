module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# A scratch buffer on the stack (PPC64LE)

`withStackScratch bytes r c` runs code `c`, written for a function whose last
argument is a scratch buffer, passed in `r`, without that argument: it
allocates a frame of `bytes` bytes on the stack (`stdu r1, -bytes(r1)`) and
passes the address of its local variable space, above the frame's 32-byte
header, in `r`. The buffer is below the stack pointer on entry, where no Rust
object lies.

`withStackScratchWiped bytes r words c` is the same, but zeroes the first
`words` doublewords of the buffer after its code (`wipe`), for a function
whose working space may hold secrets that its caller would otherwise wipe.

`withStackArgScratch bytes m c` is for a function whose scratch buffer
argument is passed on the stack, after `m` other stack arguments (its eight
argument registers all taken): it allocates a frame of `bytes` bytes and lays
out in it what `c` expects to find above `r1` on entry (the return address is
in the link register, not on the stack): after the 32-byte header and the
first 64 bytes of the Parameter Save Area, which stand for `r3`–`r10`, a
copy of the `m` stack arguments (ELFv2 ABI §2.2.3.3: the first at
`r1 + 96`), then the address of the buffer as stack argument `m`, and the
buffer right after it (`bufOff m`, so `r1 + 104 + 8m`). It passes them
through `r12` (the frame's base) and `r11`, which no argument is in.
-/

@[expose] public section

namespace VG.Impl.StackScratch.PPC64LE

open VG.PPC64LE

/-- `c`, with its scratch buffer (passed in `r`) in a frame of `bytes` bytes
on the stack, at `r1 + 32`. -/
def withStackScratch (bytes : Nat) (r : Reg) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block [.addSp r 32]) c) (.free bytes)

/-- `std r11, 8k(r12)` for each `k < words`. -/
def wipeStores (words : Nat) : List Instr :=
  (List.range words).map fun k => .store .d .r11 .r12 (8 * k)

/-- Zeroes the `words` doublewords of the buffer, at `r1 + 32`, through `r12`
(their address) and `r11` (zero). -/
def wipe (words : Nat) : List Instr := .addSp .r12 32 :: .li .r11 0 :: wipeStores words

/-- `withStackScratch`, zeroing the first `words` doublewords of the buffer
after the code. -/
def withStackScratchWiped (bytes : Nat) (r : Reg) (words : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes r (.seq c (.block (wipe words)))

/-- The offset from `r1` of the buffer of `withStackArgScratch`, after the
header, the eight doublewords of the Parameter Save Area that stand for the
argument registers, `m` stack arguments and the buffer's address. -/
def bufOff (m : Nat) : Nat := 104 + 8 * m

/-- `ld r11, bytes + 96 + 8j(r12); std r11, 96 + 8j(r12)`: copy stack argument
`j` from the caller's frame into this one (`r12` is the frame's stack
pointer). -/
def copyArg (bytes j : Nat) : List Instr :=
  [.load .d .r11 .r12 (bytes + 96 + 8 * j), .store .d .r11 .r12 (96 + 8 * j)]

/-- Copy the `m` stack arguments to the frame (its stack pointer in `r12`),
and pass the buffer, at `r1 + bufOff m`, as the next. -/
def setArgs (bytes m : Nat) : List Instr :=
  .addSp .r12 0 :: (List.range m).flatMap (copyArg bytes) ++
    [.addSp .r11 (bufOff m), .store .d .r11 .r12 (96 + 8 * m)]

/-- `c`, whose scratch buffer is passed on the stack after `m` other stack
arguments, with the buffer in a frame of `bytes` bytes on the stack. -/
def withStackArgScratch (bytes m : Nat) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (setArgs bytes m)) c) (.free bytes)

end VG.Impl.StackScratch.PPC64LE
