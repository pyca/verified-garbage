module

public import VerifiedGarbage.Impl.Sm4.X86.AesNiModes
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # SM4's chained modes by the AES S-box on x86 (32-bit): the functions as emitted

Each function with its working space in a frame on the stack, which it
wipes (`withStackScratchWiped`), then its cleanup
(`Impl.Scrub.X86.scrubSel rb W ws`): of the `W` bytes of stack below `esp`
that its contract reserves, the doublewords `ws` its code may leave
different in two runs zeroed, and the registers a callee may change
cleared, so that it returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Sm4.X86.AesNi.Fn

open VG.X86

/-- The doublewords of the 692 bytes of stack below `esp` that the residue
analysis finds each function may leave different in two runs: the header
of its working space's frame. -/
def modeWords : List Nat := [1, 2, 3, 4, 5, 6]

/-- `Spec.Sm4.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 692 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.cbcEncryptChained)

/-- `Spec.Sm4.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 692 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.ofb)

/-- `Spec.Sm4.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 692 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.ofbFinal)

/-- `Spec.Sm4.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 692 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.cfbEncrypt)

/-- `Spec.Sm4.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 692 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.cfbEncryptFinal)

/-- `Spec.Sm4.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 692 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 688 4 166 Impl.Sm4.X86.AesNi.cfbDecryptFinal)

end VG.Impl.Sm4.X86.AesNi.Fn
