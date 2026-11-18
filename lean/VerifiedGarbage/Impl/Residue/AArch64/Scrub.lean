module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Clearing the stack a function used before returning (AArch64)

`withScrub W c` runs `c`, then zeroes the `W` bytes below the stack pointer,
where `c`'s frames were: it opens a frame of `W` bytes (`sub sp, sp, #W`),
zeroes it 16 bytes at a time (`str q31, [x9, #16k]`, `x9` its base and `q31`
zero), and releases it. What `c`'s frames held is then gone from the stack
below the stack pointer, where its caller cannot clear it. `W` is a multiple
of 16, below 4096, and at most what the contract lets the function use of
the stack.
-/

@[expose] public section

namespace VG.Impl.Residue.AArch64

open VG.AArch64

/-- `str q31, [x9, #16k]` for each `k < n`. -/
def scrubStores (n : Nat) : List Instr := (List.range n).map fun k => .strq .v31 .x9 (16 * k)

/-- `movi v31.2d, #0`, `add x9, sp, #0`, then the stores of the `W` bytes from `x9`. -/
def scrubBlock (W : Nat) : List Instr := .vop (.movi0 .v31) :: .addSp .x9 0 :: scrubStores (W / 16)

/-- The frame of `W` bytes, zeroed. -/
def scrubTail (W : Nat) : Prog isa := .frame (.alloc W) (.block (scrubBlock W)) (.free W)

/-- `c`, then the `W` bytes below the stack pointer zeroed. -/
def withScrub (W : Nat) (c : Prog isa) : Prog isa := .seq c (scrubTail W)

end VG.Impl.Residue.AArch64
