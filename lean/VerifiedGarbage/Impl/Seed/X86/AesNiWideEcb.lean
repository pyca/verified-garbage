module

public import VerifiedGarbage.Impl.Seed.X86.AesNiWide
public import VerifiedGarbage.Impl.Modes.X86.Ecb
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-!
# SEED-ECB by the AES S-box on x86 (32-bit)

`ecb d`: ECB for any core (`Impl.Modes.X86.Core.ecbLevels`) over SEED's
core for four blocks in the direction `d` (`AesNiWide.lean`), by groups of
four and of two blocks, then one block at a time, with its scratch buffer as
the fourth argument. `Fn.ecbEncrypt` and `Fn.ecbDecrypt` are the functions
as emitted: with that working space in a frame on the stack, which they
wipe, then their cleanup (`Impl.Scrub.X86.scrubSel`). The frame is larger
than the working space and its header need (736 bytes for 732), so that
the working space, which `withStackScratchWiped` puts 20 bytes above the
frame's base for three arguments, is at a multiple of 16 when `esp` is one
at the call: the core's 16-byte loads and stores then cross no page, or
line of the cache.
-/

@[expose] public section

namespace VG.Impl.Seed.X86.AesNiWide

open VG.X86
open VG.Spec.Seed (Direction)

/-- `vg_seed_ecb_encrypt` or `vg_seed_ecb_decrypt`, with its scratch buffer
as the fourth argument. -/
def ecb (d : Direction) : Prog isa := (core d).ecbLevels levels

namespace Fn

/-- The doublewords of the 740 bytes of stack below `esp` that the residue
analysis finds the ECB functions may leave different in two runs: the
header of their working space's frame, and the frame's last doubleword,
which nothing writes. -/
def ecbWords : List Nat := [1, 2, 3, 4, 5, 184]

/-- `Spec.Seed.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 740 ecbWords (Impl.StackScratch.X86.withStackScratchWiped 736 3 178 (ecb .encrypt))

/-- `Spec.Seed.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 740 ecbWords (Impl.StackScratch.X86.withStackScratchWiped 736 3 178 (ecb .decrypt))

end Fn

end VG.Impl.Seed.X86.AesNiWide
