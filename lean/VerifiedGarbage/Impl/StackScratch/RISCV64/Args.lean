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

/-- `t2 := t0 + bytes`, the caller's stack arguments above the frame, in two
`addi`s (an immediate reaches only 2047, and the frame may be larger). -/
def argBase (bytes : Nat) : List Instr :=
  [.addi .t2 .t0 ((min bytes 2032 : Nat) : Int), .addi .t2 .t2 ((bytes - min bytes 2032 : Nat) : Int)]

/-- `ld t1, 8j(t2); sd t1, 8j(t0)`: copy doubleword `j` of the caller's stack
arguments (from `t2`) into the frame, whose stack pointer is in `t0`. -/
def copyArg (j : Nat) : List Instr :=
  [.load .d .t1 .t2 (8 * j), .store .d .t1 .t0 (8 * j)]

/-- Copy the `m` doublewords of stack arguments, and pass the buffer, at
`sp + 8 + 8m`, as the next. -/
def setArgs (bytes m : Nat) : List Instr :=
  [.addSp .t0 0] ++ argBase bytes ++ (List.range m).flatMap copyArg ++
    [.addi .t1 .t0 ((8 + 8 * m : Nat) : Int), .store .d .t1 .t0 (8 * m)]

/-- `c`, whose scratch buffer is the stack argument after `m` doublewords of
others, with the buffer in a frame of `bytes` bytes on the stack, at
`sp + 8 + 8m`. -/
def withStackScratchArgs (bytes m : Nat) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (setArgs bytes m)) c) (.free bytes)

end VG.Impl.StackScratch.RISCV64
