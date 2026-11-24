module

public import VerifiedGarbage.Impl.Seed.X86.Sse
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # SEED on x86 (32-bit) in XMM registers: the functions as emitted

Each function with its working space in a frame on the stack, which it
wipes (`withStackScratchWiped`), then its cleanup
(`Impl.Scrub.X86.scrubSel rb W ws`): of the `W` bytes of stack below `esp`
that its contract reserves, the doublewords `ws` its code may leave
different in two runs zeroed, and the registers a callee may change
cleared, so that it returns without secret residue.

A function's frame is larger than its working space and header need, so
that the working space is at a multiple of 16 when `esp` is one at the call:
its slots, which every round loads and stores, then cross no page, or line
of the cache. -/

@[expose] public section

namespace VG.Impl.Seed.X86.Sse

open VG.X86

namespace Fn

/-- The doublewords of the 1864 bytes of stack below `esp` that the residue
analysis finds the ECB functions may leave different in two runs: where the
core calls its functions, the header of their working space's frame, and the
frame's last doublewords, which nothing writes. -/
def ecbWords : List Nat := [0, 1, 2, 3, 4, 5, 6, 465]

/-- And of the other functions' 1868. -/
def modeWords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 466]

/-- `Spec.Seed.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1864 ecbWords (Impl.StackScratch.X86.withStackScratchWiped 1856 3 458 (ecb .encrypt))

/-- `Spec.Seed.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1864 ecbWords (Impl.StackScratch.X86.withStackScratchWiped 1856 3 458 (ecb .decrypt))

/-- `Spec.Seed.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1868 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cbcEncryptChained)

/-- `Spec.Seed.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1868 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cbcDecryptChained)

/-- `Spec.Seed.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1868 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.ofb)

/-- `Spec.Seed.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1868 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.ofbFinal)

/-- `Spec.Seed.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1868 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cfbEncrypt)

/-- `Spec.Seed.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1868 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cfbDecrypt)

/-- `Spec.Seed.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1868 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cfbEncryptFinal)

/-- `Spec.Seed.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1868 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1860 4 458 Impl.Seed.X86.Sse.cfbDecryptFinal)

end Fn

end VG.Impl.Seed.X86.Sse
