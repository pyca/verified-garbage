module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# A scratch buffer on the stack, for a function with stack arguments (RISC-V)

`withStackScratchArgs bytes m c` runs code `c`, written for a function whose
arguments fill `a0`–`a7` and `m` doublewords of stack (the psABI's "The
first argument passed on the stack is located at offset zero of the stack
pointer on function entry"), followed by a scratch buffer argument (so
passed on the stack too), without that argument: as PPC64LE's
`withStackScratchArgs` does, it allocates a frame of `bytes` bytes on the
stack (`addi sp, sp, -bytes`) and lays out in it what `c` expects to find
from `sp` on entry (`setArgs`): a copy of the `m` doublewords of arguments,
then the address of the buffer, which follows them. The buffer is below the
stack pointer on entry, where no Rust object lies.
-/

@[expose] public section

namespace VG.Impl.StackScratch.RISCV64

open VG.RISCV64

/-- The part of the offset `bytes` of the caller's stack arguments that
`copyArg` adds first, so that what is left of it fits `ld`'s immediate
(which reaches only 2047, while the frame may be larger). -/
def argStep (bytes : Nat) : Nat := min bytes 2032

/-- `addi t1, t0, argStep bytes; ld t1, bytes - argStep bytes + 8j(t1);
sd t1, 8j(t0)`: copy doubleword `j` of the caller's stack arguments into the
frame, whose stack pointer is in `t0`. -/
def copyArg (bytes j : Nat) : List Instr :=
  [.addi .t1 .t0 ((argStep bytes : Nat) : Int), .load .d .t1 .t1 (bytes - argStep bytes + 8 * j),
    .store .d .t1 .t0 (8 * j)]

/-- Copy the `m` doublewords of stack arguments, and pass the buffer, at
`sp + 8 + 8m`, as the next. -/
def setArgs (bytes m : Nat) : List Instr :=
  [.addSp .t0 0] ++ (List.range m).flatMap (copyArg bytes) ++
    [.addi .t1 .t0 ((8 + 8 * m : Nat) : Int), .store .d .t1 .t0 (8 * m)]

/-- `c`, whose scratch buffer is the stack argument after `m` doublewords of
others, with the buffer in a frame of `bytes` bytes on the stack, at
`sp + 8 + 8m`. -/
def withStackScratchArgs (bytes m : Nat) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (setArgs bytes m)) c) (.free bytes)

end VG.Impl.StackScratch.RISCV64
