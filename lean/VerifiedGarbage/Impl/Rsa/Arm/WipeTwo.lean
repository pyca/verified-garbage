module

public import VerifiedGarbage.Impl.Residue.Arm

/-!
# Zeroing more stack than one frame holds (ARMv7)

`Impl.Residue.Arm.scrubF rb n c` zeroes the `n` bytes below the stack pointer
in one frame, which the model allows only of fewer than 4096 bytes (an ARM
immediate). `scrubF2 rb a b c` zeroes `a + b` bytes in two: it opens a frame
of `a` bytes, zeroes them (`wipeBody`), zeroes the `b` bytes below it in a
frame of its own (`wipeBelow`), and releases the outer frame, then `tail rb`.
RSASSA-PKCS1-v1_5 signing with the key's precomputed values keeps 4616
bytes (its frames, and the private operation's 3440) below the stack pointer.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.WipeTwo

open VG.Arm VG.Impl.Residue.Arm

/-- Zero the `a + b` bytes below the stack pointer: `a` in a frame of them,
and the `b` below them in a frame inside it. -/
def wipeBelow2 (a b : Nat) : Prog isa := .frame (.alloc a) (.seq (wipeBody a) (wipeBelow b)) (.free a)

/-- `c`, then the `a + b` bytes below the stack pointer zeroed, then
`tail rb`: the function as emitted. -/
def scrubF2 (rb a b : Nat) (c : Prog isa) : Prog isa := .seq c (.seq (wipeBelow2 a b) (.block (tail rb)))

end VG.Impl.Rsa.Arm.WipeTwo
