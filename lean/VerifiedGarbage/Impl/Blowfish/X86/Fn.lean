module

public import VerifiedGarbage.Impl.Blowfish.X86
public import VerifiedGarbage.Impl.Blowfish.X86.Modes
public import VerifiedGarbage.Impl.Blowfish.X86.FbFinal
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # Blowfish on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`, or
`Impl.Scrub.X86.scrub rb` for code without a frame or calls): the `W` bytes
of stack below `esp` that its contract reserves zeroed, and the registers
a callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Blowfish.X86.Fn

open VG.X86

/-- The doublewords of the 84 bytes below `esp` that the residue analysis finds
`expandKey` may leave different in two runs. -/
def expandKeyWords : List Nat := [0, 1, 2, 3, 4, 15, 16, 17, 18, 19, 20]

/-- The doublewords of the 276 bytes below `esp` that the residue analysis finds
`ecbEncrypt`, `ecbDecrypt` may leave different in two runs. -/
def ecbEncryptWords : List Nat := [0, 1, 2, 3, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68]

/-- The doublewords of the 112 bytes below `esp` that the residue analysis finds
`cbcEncryptChained`, `cbcDecryptChained`, `cfbEncrypt`, `cfbDecrypt`, `cfbEncryptFinal`, `cfbDecryptFinal`, `ofb`, `ofbFinal` may leave different in two runs. -/
def cbcEncryptChainedWords : List Nat := [0, 1, 2, 3, 4, 5]

/-- `Spec.Blowfish.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 84 expandKeyWords
    (Impl.StackScratch.X86.withStackScratchWiped 84 3 10 Impl.Blowfish.X86.expandKey)

/-- `Spec.Blowfish.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 276 ecbEncryptWords
    (Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.encrypt)

/-- `Spec.Blowfish.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 276 ecbEncryptWords
    (Impl.StackScratch.X86.withStackScratchWiped 276 3 10 Impl.Blowfish.X86.decrypt)

/-- `Spec.Blowfish.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 cbcEncryptChainedWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cbcEncryptChained)

/-- `Spec.Blowfish.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 cbcEncryptChainedWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cbcDecryptChained)

/-- `Spec.Blowfish.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 cbcEncryptChainedWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbEncrypt)

/-- `Spec.Blowfish.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 cbcEncryptChainedWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbDecrypt)

/-- `Spec.Blowfish.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 cbcEncryptChainedWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbEncryptFinal)

/-- `Spec.Blowfish.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 cbcEncryptChainedWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbDecryptFinal)

/-- `Spec.Blowfish.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 cbcEncryptChainedWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.ofb)

/-- `Spec.Blowfish.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 112 cbcEncryptChainedWords
    (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.ofbFinal)

end VG.Impl.Blowfish.X86.Fn
