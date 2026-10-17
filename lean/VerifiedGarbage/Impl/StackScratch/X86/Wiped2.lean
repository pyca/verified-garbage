module

public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# A scratch buffer on the stack, zeroed in two places (x86)

`withStackScratchWiped2 bytes n a d b c` is `withStackScratch bytes n c`,
then zeroes the first `a` doublewords of the buffer and the `b` at its byte
`d` (`wipe2`), for a function whose working space may hold secrets in those
two places alone.
-/

@[expose] public section

namespace VG.Impl.StackScratch.X86

open VG.X86

/-- Zeroes the `a` doublewords at `esp + off` and the `b` at
`esp + off + d`, through `ecx`. -/
def wipe2 (off a d b : Nat) : List Instr := wipe off a ++ wipeStores (off + d) b

/-- `withStackScratch`, zeroing the first `a` doublewords of the buffer (at
`esp + 8 + 4n`) and the `b` at its byte `d` after the code. -/
def withStackScratchWiped2 (bytes n a d b : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes n (.seq c (.block (wipe2 (8 + 4 * n) a d b)))

end VG.Impl.StackScratch.X86
