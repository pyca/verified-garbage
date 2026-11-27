module

public import VerifiedGarbage.Impl.Cast5.X86
public import VerifiedGarbage.Impl.Cast5.X86.Modes
public import VerifiedGarbage.Impl.Cast5.X86.FbFinal
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # CAST5 on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubSel rb W ws`,
`Impl/Scrub/X86/Sel.lean`): of the `W` bytes of stack below `esp` that its
contract reserves, the doublewords `ws` that the residue analysis finds it
may leave different in two runs zeroed, and the registers a callee may
change cleared but the `rb` bits of the result, so that it returns without
secret residue. -/

@[expose] public section

namespace VG.Impl.Cast5.X86.Fn

open VG.X86

/-- The doublewords of the stack below `esp` that the residue analysis finds
each function may leave different in two runs: none of the 4 bytes of key
expansion's and ECB's call that finds the tables, … -/
def noWords : List Nat := []

/-- … and of the 336 bytes of the modes, the header of their frame and the
frames below it. -/
def modeWords : List Nat := [1, 2, 3, 4, 5, 6, 7]

/-- `Spec.Cast5.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 4 noWords
    (Impl.Cast5.X86.expandKey)

/-- `Spec.Cast5.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 4 noWords
    (Impl.Cast5.X86.ecbEncrypt)

/-- `Spec.Cast5.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 4 noWords
    (Impl.Cast5.X86.ecbDecrypt)

/-- `Spec.Cast5.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 336 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cbcEncryptChained)

/-- `Spec.Cast5.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 336 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cbcDecryptChained)

/-- `Spec.Cast5.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 336 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbEncrypt)

/-- `Spec.Cast5.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 336 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbDecrypt)

/-- `Spec.Cast5.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 336 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbEncryptFinal)

/-- `Spec.Cast5.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 336 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.cfbDecryptFinal)

/-- `Spec.Cast5.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 336 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.ofb)

/-- `Spec.Cast5.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 336 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 Impl.Cast5.X86.Modes.ofbFinal)

end VG.Impl.Cast5.X86.Fn
