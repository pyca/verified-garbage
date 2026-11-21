module

public import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.X86.Ecb
public import VerifiedGarbage.Impl.TripleDes.X86.Modes
public import VerifiedGarbage.Impl.TripleDes.X86.Fb
public import VerifiedGarbage.Impl.TripleDes.X86.FbFinal
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel

/-! # Triple DES on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubSel rb W ws`, or
`Impl.Scrub.X86.scrub rb` for code without a frame or calls, or whose frame
it wipes itself with nothing called in it: key expansion): of the `W` bytes
of stack below `esp` that its contract reserves, the doublewords `ws` its
code may leave different in two runs zeroed (`Impl/Scrub/X86/Sel.lean`),
and the registers a callee may change cleared but the `rb` bits of the
result, so that it returns without secret residue. -/

@[expose] public section

namespace VG.Impl.TripleDes.X86.Fn

open VG.X86

/-- `Spec.TripleDes.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrub 0 (Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.TripleDes.X86.Key.expandKey)

/-- The doublewords of the stack below `esp` that the residue analysis finds
each function may leave different in two runs: the frame header of its
working space and the frames below it, of the 1060 bytes ECB's contract
reserves, … -/
def ecbWords : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]

/-- … of the 984 bytes the modes one block at a time reserve, … -/
def blockWords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- … and of the 1248 bytes of the batched CBC and CFB64 decryption. -/
def batchWords : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- `Spec.TripleDes.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1060 ecbWords
    (Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.encrypt)

/-- `Spec.TripleDes.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1060 ecbWords
    (Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.decrypt)

/-- `Spec.TripleDes.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 984 blockWords
    (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cbcEncryptChained)

/-- `Spec.TripleDes.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1248 batchWords
    (Impl.StackScratch.X86.withStackScratchWiped 1232 4 302 Impl.TripleDes.X86.cbcDecryptChained)

/-- `Spec.TripleDes.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 984 blockWords
    (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbEncrypt)

/-- `Spec.TripleDes.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 1248 batchWords
    (Impl.StackScratch.X86.withStackScratchWiped 1232 4 302 Impl.TripleDes.X86.cfbDecrypt)

/-- `Spec.TripleDes.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 984 blockWords
    (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbEncryptFinal)

/-- `Spec.TripleDes.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 984 blockWords
    (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbDecryptFinal)

/-- `Spec.TripleDes.cfb8EncryptApi`'s function as emitted. -/
def cfb8Encrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 984 blockWords
    (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfb8Encrypt)

/-- `Spec.TripleDes.cfb8DecryptApi`'s function as emitted. -/
def cfb8Decrypt : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 984 blockWords
    (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfb8Decrypt)

/-- `Spec.TripleDes.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 984 blockWords
    (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofb)

/-- `Spec.TripleDes.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 984 blockWords
    (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofbFinal)

end VG.Impl.TripleDes.X86.Fn
