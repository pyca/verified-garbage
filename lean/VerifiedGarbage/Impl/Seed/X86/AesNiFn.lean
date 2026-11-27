module

public import VerifiedGarbage.Impl.Seed.X86.AesNiModes
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # SEED's chained modes by the AES S-box on x86 (32-bit): the functions as emitted

Each function with its working space in a frame on the stack, which it
wipes (`withStackScratchWiped`), then its cleanup
(`Impl.Scrub.X86.scrubSel rb W ws`): of the `W` bytes of stack below `esp`
that its contract reserves, the doublewords `ws` its code may leave
different in two runs zeroed, and the registers a callee may change
cleared, so that it returns without secret residue.

A frame is larger than its working space and header need (676 bytes for
672), so that the working space, which `withStackScratchWiped` puts 24
bytes above the frame's base for four arguments, is at a multiple of 16
when `esp` is one at the call: the core's 16-byte loads and stores, all at
multiples of 16 in the working space, then cross no page, or line of the
cache. -/

@[expose] public section

namespace VG.Impl.Seed.X86.AesNi.Fn

open VG.X86

/-- The doublewords of the 680 bytes of stack below `esp` that the residue
analysis finds each function may leave different in two runs: the header
of its working space's frame, and the frame's last doubleword, which
nothing writes. -/
def modeWords : List Nat := [1, 2, 3, 4, 5, 6, 169]

/-- `Spec.Seed.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 680 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 676 4 162 Impl.Seed.X86.AesNi.cbcEncryptChained)

/-- `Spec.Seed.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 680 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 676 4 162 Impl.Seed.X86.AesNi.ofb)

/-- `Spec.Seed.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 680 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 676 4 162 Impl.Seed.X86.AesNi.ofbFinal)

/-- `Spec.Seed.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 680 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 676 4 162 Impl.Seed.X86.AesNi.cfbEncrypt)

/-- `Spec.Seed.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 680 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 676 4 162 Impl.Seed.X86.AesNi.cfbEncryptFinal)

/-- `Spec.Seed.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 680 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 676 4 162 Impl.Seed.X86.AesNi.cfbDecryptFinal)

end VG.Impl.Seed.X86.AesNi.Fn
