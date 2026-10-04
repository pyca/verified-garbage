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

`withTagScratch bytes m a c` is for a function one of whose arguments (at
`a`: a register, or a stack argument) is a buffer of working space that
also carries a 16-byte tag, in or out, in its first 16 bytes: it runs `c` as
a function whose argument there is a pointer to the 16-byte tag alone. It
allocates a frame of `bytes` bytes and lays out in it what `c` expects at
and above `sp` on entry: a copy of the `m` stack arguments (there is no
return address on the stack: it is in `x30`, which neither the frame nor
`c` changes); then the tag pointer, at `sp + 8m`, and the buffer, at the
next multiple of 16, `sp + 16 (⌊m / 2⌋ + 1)`, which is the rest of the
frame. It copies the tag's 16 bytes into the buffer and passes the buffer at
`a` before the code (`tagSetup`), and copies the buffer's first 16 bytes back
to the tag after it (`tagOut`), through `x16`, `x17` and `v16`, which are
neither callee-saved nor hold a result, so that `x0` keeps the code's.
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

/-- Where a function's tag pointer is: in a register, or in stack argument
`j`. -/
inductive TagArg where
  | reg (r : Reg)
  | stack (j : Nat)
  deriving DecidableEq

/-- `ldr x17, [sp, #(bytes + 8j)]; str x17, [x16, #8j]`: copy stack
argument `j` from the caller's frame into this one, whose base is in
`x16`. -/
def copyArg (bytes j : Nat) : List Instr :=
  [.ldrSp .x17 (bytes + 8 * j), .str .x .x17 .x16 (8 * j)]

/-- The register `tagIn` reads the tag pointer from: its own, or `x17`,
into which `loadTagPtr` loads it from its stack argument. -/
def tagReg : TagArg → Reg
  | .reg r => r
  | .stack _ => .x17

/-- Load the tag pointer from the caller's stack argument into `x17`, if it
is there. -/
def loadTagPtr (bytes : Nat) : TagArg → List Instr
  | .reg _ => []
  | .stack j => [.ldrSp .x17 (bytes + 8 * j)]

/-- Save the tag pointer (in `p`) at `sp + 8m`, and copy the tag's 16 bytes
to the buffer, at `sp + 16 (⌊m / 2⌋ + 1)`, through `v16`. -/
def tagIn (m : Nat) (p : Reg) : List Instr :=
  [.str .x p .x16 (8 * m), .ldrq .v16 p 0, .strq .v16 .x16 (16 * (m / 2 + 1))]

/-- Pass the buffer in place of the tag pointer: in its register, or in the
copy of its stack argument. -/
def pointTag (m : Nat) : TagArg → List Instr
  | .reg r => [.addSp r (16 * (m / 2 + 1))]
  | .stack j => [.addSp .x17 (16 * (m / 2 + 1)), .str .x .x17 .x16 (8 * j)]

/-- Copy the `m` stack arguments, save the tag pointer, copy the tag into the
buffer and pass the buffer in the tag pointer's place. -/
def tagSetup (bytes m : Nat) (a : TagArg) : List Instr :=
  .addSp .x16 0 :: (List.range m).flatMap (copyArg bytes) ++ loadTagPtr bytes a ++
    tagIn m (tagReg a) ++ pointTag m a

/-- Copy the buffer's first 16 bytes back to the tag, whose pointer is at
`sp + 8m`, through `x16`, `x17` and `v16`. -/
def tagOut (m : Nat) : List Instr :=
  [.ldrSp .x16 (8 * m), .addSp .x17 (16 * (m / 2 + 1)), .ldrq .v16 .x17 0, .strq .v16 .x16 0]

/-- `c`, whose working space at `a` also carries a 16-byte tag, run with a
pointer to the tag alone at `a`, the working space in a frame of `bytes`
bytes on the stack, after a copy of the `m` stack arguments and the tag
pointer. -/
def withTagScratch (bytes m : Nat) (a : TagArg) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (tagSetup bytes m a)) (.seq c (.block (tagOut m))))
    (.free bytes)

end VG.Impl.StackScratch.AArch64
