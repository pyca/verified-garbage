module

public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# A scratch buffer on the stack, wiped two doublewords at a time (AArch64)

`withStackScratchWipedPairs bytes r pairs c` is `withStackScratchWiped bytes r
(2 * pairs) c`, but zeroes the doublewords with `stp x17, x17`: half as many
store instructions as `str x17` for the same bytes. `stp` takes offsets up to
504, so the pairs go in chunks of 32 (512 bytes), each from `x16` set to `sp`
plus the chunk's offset.
-/

@[expose] public section

namespace VG.Impl.StackScratch.AArch64

open VG.AArch64

/-- `stp x17, x17, [x16, #16k]` for each `k < pairs`. -/
def wipePairStores (pairs : Nat) : List Instr :=
  (List.range pairs).map fun k => .stp .x17 .x17 .x16 (16 * k)

/-- Chunk `j`: `x16` set to `sp + 512 j`, then `pairs` pairs (at most 32)
from there. -/
def wipePairChunk (j pairs : Nat) : List Instr := .addSp .x16 (512 * j) :: wipePairStores pairs

/-- The chunks of `pairs` pairs: `pairs / 32` of 32, then the rest if any. -/
def wipePairChunks (pairs : Nat) : List Instr :=
  (List.range (pairs / 32)).flatMap (fun j => wipePairChunk j 32) ++
    if pairs % 32 = 0 then [] else wipePairChunk (pairs / 32) (pairs % 32)

/-- Zeroes the `2 * pairs` doublewords at `sp`, through `x16` (their address)
and `x17` (zero). -/
def wipePairs (pairs : Nat) : List Instr := .movz .x .x17 0 0 :: wipePairChunks pairs

/-- `withStackScratch`, zeroing the first `2 * pairs` doublewords of the
buffer after the code. -/
def withStackScratchWipedPairs (bytes : Nat) (r : Reg) (pairs : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes r (.seq c (.block (wipePairs pairs)))

end VG.Impl.StackScratch.AArch64
