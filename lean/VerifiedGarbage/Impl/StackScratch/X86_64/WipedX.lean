module

public import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# A scratch buffer on the stack, its start zeroed with 16-byte stores (x86-64)

`withStackScratchWipedX bytes r n c` is `withStackScratch bytes r c`, then
zeroes the first `n` 16-byte words of the buffer (at `rsp + 8`) with half as
many stores as `withStackScratchWiped` (`wipeAtX`, SSE2's `pxor` and
`movdqu`), for a function whose working space may hold secrets in its first
`16 n` bytes; `withStackScratchWipedX2 bytes r a d b c` zeroes the first
`a` 16-byte words and the `b` at byte `d` of the buffer (`wipeAtX2`), for
one whose secrets are in those two places.
-/

@[expose] public section

namespace VG.Impl.StackScratch.X86_64

open VG.X86_64

/-- `withStackScratch`, zeroing the first `n` 16-byte words of the buffer
(at `rsp + 8`) after the code. -/
def withStackScratchWipedX (bytes : Nat) (r : Reg) (n : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes r (.seq c (.block (wipeAtX 8 n)))

/-- Zeroes the `a` 16-byte words at `rsp + off` and the `b` at
`rsp + off + d`, through `xmm0`. -/
def wipeAtX2 (off a d b : Nat) : List Instr := wipeAtX off a ++ wipeStoresAtX (off + d) b

/-- `withStackScratch`, zeroing the first `a` 16-byte words of the buffer (at
`rsp + 8`) and the `b` at its byte `d` after the code. -/
def withStackScratchWipedX2 (bytes : Nat) (r : Reg) (a d b : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes r (.seq c (.block (wipeAtX2 8 a d b)))

end VG.Impl.StackScratch.X86_64
