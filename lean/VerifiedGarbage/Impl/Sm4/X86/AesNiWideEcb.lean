module

public import VerifiedGarbage.Impl.Sm4.X86.AesNiWide
public import VerifiedGarbage.Impl.Modes.X86.Ecb
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-!
# SM4-ECB by the AES S-box on x86 (32-bit)

`ecb d`: ECB for any core (`Impl.Modes.X86.Core.ecbLevels`) over SM4's
core for four blocks in the direction `d` (`AesNiWide.lean`), by groups of
four and of two blocks, then one block at a time, with its scratch buffer as
the fourth argument. `Fn.ecbEncrypt` and `Fn.ecbDecrypt` are the functions
as emitted: with that working space in a frame on the stack, which they
wipe, then their cleanup (`Impl.Scrub.X86.scrubSel`).
-/

@[expose] public section

namespace VG.Impl.Sm4.X86.AesNiWide

open VG.X86

/-- `vg_sm4_ecb_encrypt` or `vg_sm4_ecb_decrypt`, with its scratch buffer as
the fourth argument. -/
def ecb (d : Dir) : Prog isa := (core d).ecbLevels levels

namespace Fn

/-- The doublewords of the 752 bytes of stack below `esp` that the residue
analysis finds the ECB functions may leave different in two runs: the
header of their working space's frame. -/
def ecbWords : List Nat := [1, 2, 3, 4, 5]

/-- `Spec.Sm4.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 752 ecbWords (Impl.StackScratch.X86.withStackScratchWiped 748 3 182 (ecb .encrypt))

/-- `Spec.Sm4.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 752 ecbWords (Impl.StackScratch.X86.withStackScratchWiped 748 3 182 (ecb .decrypt))

end Fn

end VG.Impl.Sm4.X86.AesNiWide
