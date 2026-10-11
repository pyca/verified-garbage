module

public import VerifiedGarbage.TCB.Arm.Isa

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
-/

@[expose] public section

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

end VG.Impl.StackScratch.Arm
