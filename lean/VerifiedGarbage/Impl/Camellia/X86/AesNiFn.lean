module

public import VerifiedGarbage.Impl.Camellia.X86.AesNiModes
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # Camellia's chained modes by the AES S-box on x86 (32-bit): the functions as emitted

Each function with its working space in a frame on the stack, which it
wipes (`withStackScratchWiped`), then its cleanup
(`Impl.Scrub.X86.scrubSel rb W ws`): of the `W` bytes of stack below `esp`
that its contract reserves, the doublewords `ws` its code may leave
different in two runs zeroed, and the registers a callee may change
cleared, so that it returns without secret residue.

A frame is larger than its working space and header need (576 bytes for
572), so that the working space, which `withStackScratchWiped` puts 28
bytes above the frame's base for five arguments, is at an address 8 modulo
16 when `esp` is a multiple of 16 at the call: the block, at byte 8 of the
working space, and the keys, 16 bytes each from byte 24 on, are then at
multiples of 16, and the core's 16-byte loads and stores cross no page, or
line of the cache. -/

@[expose] public section

namespace VG.Impl.Camellia.X86.AesNi.Fn

open VG.X86

/-- The doublewords of the 580 bytes of stack below `esp` that the residue
analysis finds each function may leave different in two runs: the header
of its working space's frame, and the frame's last doubleword, which
nothing writes. -/
def modeWords : List Nat := [1, 2, 3, 4, 5, 6, 7, 144]

/-- `Spec.Camellia.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 576 5 136 Impl.Camellia.X86.AesNi.cbcEncryptChained)

/-- `Spec.Camellia.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 576 5 136 Impl.Camellia.X86.AesNi.ofb)

/-- `Spec.Camellia.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 576 5 136 Impl.Camellia.X86.AesNi.ofbFinal)

/-- `Spec.Camellia.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 576 5 136 Impl.Camellia.X86.AesNi.cfbEncrypt)

/-- `Spec.Camellia.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 576 5 136 Impl.Camellia.X86.AesNi.cfbEncryptFinal)

/-- `Spec.Camellia.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 580 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 576 5 136 Impl.Camellia.X86.AesNi.cfbDecryptFinal)

end VG.Impl.Camellia.X86.AesNi.Fn
