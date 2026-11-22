module

public import VerifiedGarbage.Impl.Sm4.X86.AesNiWide
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # SM4's wide modes by the AES S-box on x86 (32-bit): the functions as emitted

Each function with its working space in a frame on the stack, which it
wipes (`withStackScratchWiped`), then its cleanup
(`Impl.Scrub.X86.scrubSel rb W ws`): of the `W` bytes of stack below `esp`
that its contract reserves, the doublewords `ws` its code may leave
different in two runs zeroed, and the registers a callee may change
cleared, so that it returns without secret residue. `ctrFramed` is CTR's
code in its frame without that cleanup, the internal function that
`vg_sm4_ctr_final` calls and cleans up after (`Impl.Sm4.X86.Fn.ctrFinal`,
with the doublewords `ctrFinalWords`). -/

@[expose] public section

namespace VG.Impl.Sm4.X86.AesNiWide

open VG.X86

/-- `vg_sm4_ctr`'s code, with its working space on the stack: called as an
internal function of its own, `vg_sm4_ctr_core_aesni`. -/
def ctrFramed : Prog isa := Impl.StackScratch.X86.withStackScratchWiped 752 4 182 ctr

namespace Fn

/-- The doublewords of the 756 bytes of stack below `esp` that the residue
analysis finds each function may leave different in two runs: the header
of its working space's frame. -/
def modeWords : List Nat := [1, 2, 3, 4, 5, 6]

/-- And of the 1592 bytes of `vg_sm4_ctr_final` calling `ctrFramed`: the
header of that call's frame, and what the baseline's leaves of its own. -/
def ctrFinalWords : List Nat :=
  [191, 192, 193, 194, 195, 196, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389]

/-- `Spec.Sm4.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 756 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 752 4 182 Impl.Sm4.X86.AesNiWide.cbcDecryptChained)

/-- `Spec.Sm4.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 756 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 752 4 182 Impl.Sm4.X86.AesNiWide.cfbDecrypt)

/-- `Spec.Sm4.ctrApi`'s function as emitted. -/
def ctr : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 756 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 752 4 182 Impl.Sm4.X86.AesNiWide.ctr)

end Fn

end VG.Impl.Sm4.X86.AesNiWide
