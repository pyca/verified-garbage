module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# A scratch buffer on the stack, for a function with stack arguments (PPC64LE)

`withStackScratchArgs bytes m c` runs code `c`, written for a function whose
arguments fill `r3`–`r10` and `m` doublewords of the caller's Parameter Save
Area (ELFv2 ABI §2.2.3.3), followed by a scratch buffer argument (so passed
on the stack too), without that argument: as ARMv7's `withStackScratch`
does, it allocates a frame of `bytes` bytes on the stack (`stdu r1,
-bytes(r1)`) and lays out in it what `c` expects to find above `r1` on entry
(`setArgs`): at `r1 + 96`, doubleword 8 of the frame's own Parameter Save
Area (at `r1 + 32`), a copy of the `m` doublewords of arguments, then the
address of the buffer, which follows them. The buffer is below the stack
pointer on entry, where no Rust object lies.
-/

@[expose] public section

namespace VG.Impl.StackScratch.PPC64LE

open VG.PPC64LE

/-- `ld r0, bytes + 96 + 8j(r12); std r0, 96 + 8j(r12)`: copy doubleword `j`
of the caller's stack arguments into the frame, whose stack pointer is in
`r12`. -/
def copyArg (bytes j : Nat) : List Instr :=
  [.load .d .r0 .r12 (bytes + 96 + 8 * j), .store .d .r0 .r12 (96 + 8 * j)]

/-- Copy the `m` doublewords of stack arguments, and pass the buffer, at
`r1 + 104 + 8m`, as the next. -/
def setArgs (bytes m : Nat) : List Instr :=
  [.addSp .r12 0] ++ (List.range m).flatMap (copyArg bytes) ++
    [.addi .r0 .r12 (104 + 8 * m), .store .d .r0 .r12 (96 + 8 * m)]

/-- `c`, whose scratch buffer is the stack argument after `m` doublewords of
others, with the buffer in a frame of `bytes` bytes on the stack, at
`r1 + 104 + 8m`. -/
def withStackScratchArgs (bytes m : Nat) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block (setArgs bytes m)) c) (.free bytes)

end VG.Impl.StackScratch.PPC64LE
