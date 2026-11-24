module

public import VerifiedGarbage.Impl.Seed.X86.AesNiWide
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # SEED's wide modes by the AES S-box on x86 (32-bit): the functions as emitted

Each function with its working space in a frame on the stack, which it
wipes (`withStackScratchWiped`), then its cleanup
(`Impl.Scrub.X86.scrubSel rb W ws`): of the `W` bytes of stack below `esp`
that its contract reserves, the doublewords `ws` its code may leave
different in two runs zeroed, and the registers a callee may change
cleared, so that it returns without secret residue.

A frame is larger than its working space and header need (740 bytes for
736), so that the working space, which `withStackScratchWiped` puts 24
bytes above the frame's base for four arguments, is at a multiple of 16
when `esp` is one at the call: the core's 16-byte loads and stores then
cross no page, or line of the cache. -/

@[expose] public section

namespace VG.Impl.Seed.X86.AesNiWide.Fn

open VG.X86

/-- The doublewords of the 744 bytes of stack below `esp` that the residue
analysis finds each function may leave different in two runs: the header
of its working space's frame, and the frame's last doubleword, which
nothing writes. -/
def modeWords : List Nat := [1, 2, 3, 4, 5, 6, 185]

/-- `Spec.Seed.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 744 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 740 4 178 Impl.Seed.X86.AesNiWide.cbcDecryptChained)

/-- `Spec.Seed.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 744 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 740 4 178 Impl.Seed.X86.AesNiWide.cfbDecrypt)

end VG.Impl.Seed.X86.AesNiWide.Fn
