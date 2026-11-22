module

public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# A scratch buffer on the stack (PPC64LE)

`withStackScratch bytes r c` runs code `c`, written for a function whose last
argument is a scratch buffer, passed in `r`, without that argument: it
allocates a frame of `bytes` bytes on the stack (`stdu r1, -bytes(r1)`) and
passes the address of its local variable space, above the frame's 32-byte
header, in `r`. The buffer is below the stack pointer on entry, where no Rust
object lies.

`withStackScratchWiped bytes r words c` is the same, but zeroes the first
`words` doublewords of the buffer after its code (`wipe`), for a function
whose working space may hold secrets that its caller would otherwise wipe.
-/

@[expose] public section

namespace VG.Impl.StackScratch.PPC64LE

open VG.PPC64LE

/-- `c`, with its scratch buffer (passed in `r`) in a frame of `bytes` bytes
on the stack, at `r1 + 32`. -/
def withStackScratch (bytes : Nat) (r : Reg) (c : Prog isa) : Prog isa :=
  .frame (.alloc bytes) (.seq (.block [.addSp r 32]) c) (.free bytes)

/-- `std r11, 8k(r12)` for each `k < words`. -/
def wipeStores (words : Nat) : List Instr :=
  (List.range words).map fun k => .store .d .r11 .r12 (8 * k)

/-- The size from which `wipe` zeroes by `dcbz`. -/
def wipeCut : Nat := 1024

/-- Zeroes the `words` doublewords of the buffer, at `r1 + 32`, through `r12`
(their address) and `r0` (zero), as the clearing of `scrubAll` zeroes its
frames' regions (`Impl.Scrub.PPC64LE.zeroRegionAt`): by `std`s for fewer than
`wipeCut` bytes, else by `dcbz`s of the 128-byte blocks within them and `std`s
of the rest. -/
def wipe (words : Nat) : List Instr :=
  .addSp .r12 32 :: .li .r0 0 :: Impl.Scrub.PPC64LE.zeroRegionAt wipeCut (8 * words)

/-- `withStackScratch`, zeroing the first `words` doublewords of the buffer
after the code. -/
def withStackScratchWiped (bytes : Nat) (r : Reg) (words : Nat) (c : Prog isa) : Prog isa :=
  withStackScratch bytes r (.seq c (.block (wipe words)))

end VG.Impl.StackScratch.PPC64LE
