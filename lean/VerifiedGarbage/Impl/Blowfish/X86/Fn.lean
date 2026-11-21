module

public import VerifiedGarbage.Impl.Blowfish.X86
public import VerifiedGarbage.Impl.Blowfish.X86.Modes
public import VerifiedGarbage.Impl.Blowfish.X86.FbFinal
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # Blowfish on x86 (32-bit): the functions as emitted

Each function, then its cleanup, so that it returns without secret residue:
the registers a callee may change cleared but the `rb` bits of the result,
and of the `W` bytes of stack below `esp` that its contract reserves, all
(`Impl.Scrub.X86.scrubAll rb W`: the key expansion and ECB, which leave most
of their frames different in two runs, so that zeroing them in 16-byte
stores takes fewer stores) or the doublewords `ws` that the residue analysis
finds it may leave different in two runs (`Impl.Scrub.X86.scrubSel rb W ws`,
`Impl/Scrub/X86/Sel.lean`: the modes). -/

@[expose] public section

namespace VG.Impl.Blowfish.X86.Fn

open VG.X86

/-- The doublewords of the 112 bytes below `esp` that the residue analysis finds
`cbcEncryptChained`, `cbcDecryptChained`, `cfbEncrypt`, `cfbDecrypt`, `cfbEncryptFinal`, `cfbDecryptFinal`, `ofb`, `ofbFinal` may leave different in two runs. -/
def modeWords : List Nat := [0, 1, 2, 3, 4, 5]

/-- `Spec.Blowfish.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 84 (Impl.StackScratch.X86.withStackScratchWiped 84 3 10 Impl.Blowfish.X86.expandKey)

/-- `Spec.Blowfish.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 276 (Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.encrypt)

/-- `Spec.Blowfish.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 276 (Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.decrypt)

/-- `Spec.Blowfish.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cbcEncryptChained)

/-- `Spec.Blowfish.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cbcDecryptChained)

/-- `Spec.Blowfish.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbEncrypt)

/-- `Spec.Blowfish.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbDecrypt)

/-- `Spec.Blowfish.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbEncryptFinal)

/-- `Spec.Blowfish.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbDecryptFinal)

/-- `Spec.Blowfish.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.ofb)

/-- `Spec.Blowfish.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 modeWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.ofbFinal)

end VG.Impl.Blowfish.X86.Fn
