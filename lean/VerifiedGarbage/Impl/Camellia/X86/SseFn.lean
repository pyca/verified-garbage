module

public import VerifiedGarbage.Impl.Camellia.X86.Sse
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # Camellia on x86 (32-bit) in XMM registers: the functions as emitted

Each function with its working space in a frame on the stack, which it
wipes (`withStackScratchWiped`), then its cleanup
(`Impl.Scrub.X86.scrubSel rb W ws`): of the `W` bytes of stack below `esp`
that its contract reserves, the doublewords `ws` its code may leave
different in two runs zeroed, and the registers a callee may change
cleared, so that it returns without secret residue.

A function's frame is larger than its working space and header need where
that puts the working space at a multiple of 16 when `esp` is one at the
call: its slots, which every round loads and stores, then cross no page, or
line of the cache. `ctrFramed`'s frame has no bytes to spare:
`vg_camellia_ctr_final` calls it from a frame of its own. -/

@[expose] public section

namespace VG.Impl.Camellia.X86.Sse

open VG.X86

/-- `vg_camellia_ctr`'s code, with its working space on the stack: called
as an internal function of its own, `vg_camellia_ctr_core`. -/
def ctrFramed : Prog isa := Impl.StackScratch.X86.withStackScratchWiped 1572 5 386 ctr

namespace Fn

/-- The doublewords of the 1576 bytes of stack below `esp` that the residue
analysis finds the ECB functions may leave different in two runs: where the
core calls the block function, the
header of their working space's frame, and the frame's last doubleword,
which nothing writes. -/
def ecbWords : List Nat := [0, 1, 2, 3, 4, 5, 6, 393]

/-- And of the other functions' 1580. -/
def modeWords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 394]

/-- And of the 1660 bytes of `vg_camellia_ctr_final` calling `ctrFramed`:
where the core calls the block function, the header of that call's frame,
and that call's frame and `vg_camellia_ctr_final`'s own above it. -/
def ctrFinalWords : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406]

/-- `Spec.Camellia.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1576 ecbWords (Impl.StackScratch.X86.withStackScratchWiped 1572 4 386 (ecb .encrypt))

/-- `Spec.Camellia.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1576 ecbWords (Impl.StackScratch.X86.withStackScratchWiped 1572 4 386 (ecb .decrypt))

/-- `Spec.Camellia.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cbcEncryptChained)

/-- `Spec.Camellia.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cbcDecryptChained)

/-- `Spec.Camellia.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cfbEncrypt)

/-- `Spec.Camellia.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cfbDecrypt)

/-- `Spec.Camellia.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cfbEncryptFinal)

/-- `Spec.Camellia.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.cfbDecryptFinal)

/-- `Spec.Camellia.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.ofb)

/-- `Spec.Camellia.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.ofbFinal)

/-- `Spec.Camellia.ctrApi`'s function as emitted. -/
def ctr : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 1576 5 386 Impl.Camellia.X86.Sse.ctr)

end Fn

end VG.Impl.Camellia.X86.Sse
