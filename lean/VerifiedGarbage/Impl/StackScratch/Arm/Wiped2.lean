module

public import VerifiedGarbage.Impl.StackScratch.Arm

/-!
# A scratch buffer on the stack, after stack arguments, zeroed in two places (ARMv7)

`withStackScratchWiped2 bytes m a d b c` is `withStackScratch bytes m c`,
then zeroes the first `a` words of the buffer and the `b` at its byte `d`
(`wipe2At`), for a function whose working space may hold secrets in those
two places alone.
-/

@[expose] public section

namespace VG.Impl.StackScratch.Arm

open VG.Arm

/-- `str r2, [r12, #(d + 4k)]` for each `k < words`. -/
def wipeStoresAt (d words : Nat) : List Instr :=
  (List.range words).map fun k => .str .r2 .r12 (d + 4 * k)

/-- Zeroes the `a` words at `sp + off` and the `b` at `sp + off + d`, through
`r12` (`sp + off`) and `r2` (zero). -/
def wipe2At (off a d b : Nat) : List Instr := wipeAt off a ++ wipeStoresAt d b

/-- `withStackScratch`, zeroing the first `a` words of the buffer (at
`sp + 4m + 8`) and the `b` at its byte `d` after the code. -/
def withStackScratchWiped2 (bytes m a d b : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes m (.seq c (.block (wipe2At (4 * m + 8) a d b)))

end VG.Impl.StackScratch.Arm
