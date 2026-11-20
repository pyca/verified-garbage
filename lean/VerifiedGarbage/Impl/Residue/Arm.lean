module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Impl.StackScratch.Arm

/-!
# Clearing registers and the stack a function used before returning (ARMv7)

`scrub rb c` runs `c`, then sets the registers a callee may change, but the
`rb` bits of the result, and the flags to constants (`tail`): `r2`, `r3` and
`r12` to zero, the flags to those of comparing zero with itself, and of the
result `r1 ++ r0` what is above its `rb` bits to zero (`r1` for a result of
32 bits, both for no result). The calling convention restores `r4`–`r11`,
`lr` and `sp`, so these are all that `c` may leave secret in registers.

`scrubF rb n c` also zeroes the `n` bytes below the stack pointer, where
`c`'s frames were, before the tail: it opens a frame of `n` bytes, zeroes its
every word (`wipeBelow`: from 64 bytes by a loop of eight stores a pass,
`wipeLoop`, the shorter code there, and below by a store for each word), and
releases it. `n` is a frame size of the model, a multiple of 8 below 4096,
and at most what the contract lets the function use of the stack.

A function's code as emitted is one of these applied to its body, defined
in `Impl/` (`Impl.Sm3.Arm.Fn`); `Proof/Framework/Arm/ScrubProved.lean` states
what makes it return without secret residue.
-/

@[expose] public section

namespace VG.Impl.Residue.Arm

open VG.Arm VG.Impl.StackScratch.Arm

/-- Zero what of the result `r1 ++ r0` is above its `rb` bits. -/
def retFix (rb : Nat) : List Instr :=
  if rb = 0 then [.mov .r0 (.imm 0), .mov .r1 (.imm 0)]
  else if rb ≤ 32 then [.mov .r1 (.imm 0)] else []

/-- Set the registers a callee may change, but the result, and the flags to
constants. -/
def tail (rb : Nat) : List Instr :=
  retFix rb ++ [.mov .r2 (.imm 0), .mov .r3 (.imm 0), .mov .r12 (.imm 0), .cmp .r2 (.reg .r2)]

/-- `c`, then `tail rb`: the function as emitted, for code without frames. -/
def scrub (rb : Nat) (c : Prog isa) : Prog isa := .seq c (.block (tail rb))

/-- One pass of the looped wipe: the 8 words at `r12` zeroed, `r12` past
them, and `r3`, the passes left, one fewer, which the flags then say is zero
or not. -/
def wipeChunk : List Instr :=
  wipeStores 8 ++ [.dp .add .r12 .r12 (.imm 32), .subs .r3 .r3 (.imm 1)]

/-- The `n` bytes at the stack pointer zeroed by a loop: `n / 32` passes of
`wipeChunk`, then a store for each word of what is left. -/
def wipeLoop (n : Nat) : Prog isa :=
  .seq (.block [.addSp .r12 0, .mov .r2 (.imm 0), .mov .r3 (.imm (BitVec.ofNat 32 (n / 32)))])
    (.seq (.loop (.block wipeChunk) .ne) (.block (wipeStores (n % 32 / 4))))

/-- The `n` bytes at the stack pointer zeroed: by a loop from 64 bytes, from
where it is the shorter code, and below by a store for each word. -/
def wipeBody (n : Nat) : Prog isa :=
  if 64 ≤ n then wipeLoop n else .block (wipe (n / 4))

/-- Zero the `n` bytes below the stack pointer, in a frame of them. -/
def wipeBelow (n : Nat) : Prog isa := .frame (.alloc n) (wipeBody n) (.free n)

/-- `c`, then the `n` bytes below the stack pointer zeroed, then `tail rb`:
the function as emitted, for code with frames. -/
def scrubF (rb n : Nat) (c : Prog isa) : Prog isa := .seq c (.seq (wipeBelow n) (.block (tail rb)))

end VG.Impl.Residue.Arm
