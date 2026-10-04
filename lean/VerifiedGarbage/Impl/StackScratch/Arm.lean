import VerifiedGarbage.TCB.Arm.Isa

/-!
# A scratch buffer on the stack (ARMv7)

`withStackScratch bytes m c` runs code `c`, written for a function whose
stack arguments take `m` four-byte slots followed by a scratch buffer
argument (also on the stack), without that argument: it allocates a frame of
`bytes` bytes on the stack and lays out in it what `c` expects to find at and
above `sp` on entry: a copy of the function's stack arguments, then the
address of the buffer, which follows a word holding `lr` (the register the
copy goes through) and fills the rest of the frame. `withRegScratch bytes r c`
is the same for a function whose buffer argument is passed in a register `r`
(and the others in registers too): the buffer is the frame, whose address it
passes in `r`. `withRegScratchWiped bytes r words c` is `withRegScratch`, but
zeroes the first `words` words of the buffer after its code (`wipe`), for a
function whose working space may hold secrets that its caller would
otherwise wipe; `withStackScratchWiped bytes m words c` is the same for
`withStackScratch` (`wipeAt`, from the buffer's offset).

`withTagScratch bytes m j off c` is for a function one of whose arguments,
passed in stack slot `j` (of its `m` slots of stack arguments), is a buffer
of working space that also carries a 16-byte tag, in or out, in its first 16
bytes: it runs `c` as a function whose argument there is a pointer to the
16-byte tag alone. As `withStackScratch`, it allocates a frame of `bytes`
bytes and lays out in it what `c` expects at and above `sp` on entry, a copy
of the stack arguments, and saves `lr` after it, at `sp + 4m + 4`; the
buffer is at `sp + off`. Before the code (`tagSetup`), it copies the tag's 16
bytes into the buffer, through `lr`, reloading the tag pointer from the
caller's stack slot for each word (`tagWordIn`), passes the buffer in the
copy of slot `j`, and restores `lr`. After the code (`tagOut`), it loads the
tag pointer from the caller's slot again, into `r12`, and copies the buffer's
first 16 bytes back to the tag through `r2`: neither holds a result.
-/

namespace VG.Impl.StackScratch.Arm

open VG.Arm

/-- `ldr lr, [sp, #bytes + 4j]; str lr, [r12, #4j]`: copy stack argument slot
`j` from the caller's frame into this one (at `r12`, the frame's base). -/
def copyArg (bytes j : Nat) : List Instr :=
  [.ldrSp .lr (bytes + 4 * j), .str .lr .r12 (4 * j)]

/-- Save `lr` at `sp + 4m + 4`, copy the `m` stack argument slots, pass the
buffer, at `sp + 4m + 8`, as the next stack argument, and restore `lr`. -/
def setArgs (bytes m : Nat) : List Instr :=
  [.addSp .r12 0, .str .lr .r12 (4 * m + 4)] ++ (List.range m).flatMap (copyArg bytes) ++
    [.addSp .lr (4 * m + 8), .str .lr .r12 (4 * m), .ldrSp .lr (4 * m + 4)]

/-- `c`, with its scratch buffer in a frame of `bytes` bytes on the stack. -/
def withStackScratch (bytes m : Nat) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (setArgs bytes m)) c) (.free bytes)

/-- `c`, whose scratch buffer is passed in `r`, with the buffer in a frame of
`bytes` bytes on the stack, at `sp`. -/
def withRegScratch (bytes : Nat) (r : Reg) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block [.addSp r 0]) c) (.free bytes)

/-- `str r2, [r12, #4k]` for each `k < words`. -/
def wipeStores (words : Nat) : List Instr :=
  (List.range words).map fun k => .str .r2 .r12 (4 * k)

/-- Zeroes the `words` words at `sp`, through `r12` (their address) and `r2`
(zero). -/
def wipe (words : Nat) : List Instr := .addSp .r12 0 :: .mov .r2 (.imm 0) :: wipeStores words

/-- `withRegScratch`, zeroing the first `words` words of the buffer after the
code. -/
def withRegScratchWiped (bytes : Nat) (r : Reg) (words : Nat) (c : Prog isa) : Prog isa :=
  withRegScratch bytes r (.seq c (.block (wipe words)))

/-- Zeroes the `words` words at `sp + off`, through `r12` (their address) and
`r2` (zero). -/
def wipeAt (off words : Nat) : List Instr :=
  .addSp .r12 off :: .mov .r2 (.imm 0) :: wipeStores words

/-- `withStackScratch`, zeroing the first `words` words of the buffer (at
`sp + 4m + 8`) after the code. -/
def withStackScratchWiped (bytes m words : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes m (.seq c (.block (wipeAt (4 * m + 8) words)))

/-- `ldr lr, [sp, #bytes + 4j]; ldr lr, [lr, #4k]; str lr, [r12, #off + 4k]`:
copy word `k` of the tag, whose pointer is in the caller's stack slot `j`, to
the buffer at `r12 + off` (`r12` is the frame's base). -/
def tagWordIn (bytes j off k : Nat) : List Instr :=
  [.ldrSp .lr (bytes + 4 * j), .ldr .lr .lr (4 * k), .str .lr .r12 (off + 4 * k)]

/-- Save `lr` at `sp + 4m + 4`, copy the `m` stack argument slots and the
tag (from the pointer in slot `j`) into the buffer at `sp + off`, pass the
buffer in the copy of slot `j`, and restore `lr`. -/
def tagSetup (bytes m j off : Nat) : List Instr :=
  [.addSp .r12 0, .str .lr .r12 (4 * m + 4)] ++ (List.range m).flatMap (copyArg bytes) ++
    (List.range 4).flatMap (tagWordIn bytes j off) ++
    [.addSp .lr off, .str .lr .r12 (4 * j), .ldrSp .lr (4 * m + 4)]

/-- `ldr r2, [sp, #off + 4k]; str r2, [r12, #4k]`: copy word `k` of the
buffer at `sp + off` to the tag at `r12`. -/
def tagWordOut (off k : Nat) : List Instr := [.ldrSp .r2 (off + 4 * k), .str .r2 .r12 (4 * k)]

/-- Load the tag pointer from the caller's stack slot `j` into `r12`, and copy
the buffer's first 16 bytes (at `sp + off`) to the tag, through `r2`. -/
def tagOut (bytes j off : Nat) : List Instr :=
  .ldrSp .r12 (bytes + 4 * j) :: (List.range 4).flatMap (tagWordOut off)

/-- `c`, whose working space, passed in stack slot `j` of `m`, also carries a
16-byte tag, run with a pointer to the tag alone in that slot, the working
space at `sp + off` in a frame of `bytes` bytes on the stack, after a copy of
the stack arguments and the saved `lr`. -/
def withTagScratch (bytes m j off : Nat) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes)
    (.seq (.block (tagSetup bytes m j off)) (.seq c (.block (tagOut bytes j off)))) (.free bytes)

end VG.Impl.StackScratch.Arm
