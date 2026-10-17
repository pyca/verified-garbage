module

public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# A scratch buffer on the stack, zeroed in two places (AArch64)

`withStackScratchWiped2 bytes r a d b c` is `withStackScratch bytes r c`,
then zeroes the first `a` doublewords of the buffer and the `b` at its byte
`d` (`wipe2`), for a function whose working space may hold secrets in those
two places alone.
-/

@[expose] public section

namespace VG.Impl.StackScratch.AArch64

open VG.AArch64

/-- `str x17, [x16, #(d + 8k)]` for each `k < words`. -/
def wipeStoresAt (d words : Nat) : List Instr :=
  (List.range words).map fun k => .str .x .x17 .x16 (d + 8 * k)

/-- Zeroes the `a` doublewords at `sp` and the `b` at `sp + d`, through `x16`
(`sp`) and `x17` (zero). -/
def wipe2 (a d b : Nat) : List Instr := wipe a ++ wipeStoresAt d b

/-- `withStackScratch`, zeroing the first `a` doublewords of the buffer and
the `b` at its byte `d` after the code. -/
def withStackScratchWiped2 (bytes : Nat) (r : Reg) (a d b : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes r (.seq c (.block (wipe2 a d b)))

end VG.Impl.StackScratch.AArch64
