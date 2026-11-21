module

public import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.X86.Ecb
public import VerifiedGarbage.Impl.TripleDes.X86.Modes
public import VerifiedGarbage.Impl.TripleDes.X86.Fb
public import VerifiedGarbage.Impl.TripleDes.X86.FbFinal
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-! # Triple DES on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`, or
`Impl.Scrub.X86.scrub rb` for code without a frame or calls, or whose frame
it wipes itself with nothing called in it: key expansion): the `W` bytes
of stack below `esp` that its contract reserves zeroed, and the registers
a callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.TripleDes.X86.Fn

open VG.X86

/-- `Spec.TripleDes.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrub 0 (Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.TripleDes.X86.Key.expandKey)

/-- `Spec.TripleDes.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 1060 (Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.encrypt)

/-- `Spec.TripleDes.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 1060 (Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.decrypt)

/-- `Spec.TripleDes.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 984 (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cbcEncryptChained)

/-- `Spec.TripleDes.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 1248 (Impl.StackScratch.X86.withStackScratchWiped 1232 4 302 Impl.TripleDes.X86.cbcDecryptChained)

/-- `Spec.TripleDes.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 984 (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbEncrypt)

/-- `Spec.TripleDes.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 1248 (Impl.StackScratch.X86.withStackScratchWiped 1232 4 302 Impl.TripleDes.X86.cfbDecrypt)

/-- `Spec.TripleDes.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 984 (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbEncryptFinal)

/-- `Spec.TripleDes.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 984 (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbDecryptFinal)

/-- `Spec.TripleDes.cfb8EncryptApi`'s function as emitted. -/
def cfb8Encrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 984 (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfb8Encrypt)

/-- `Spec.TripleDes.cfb8DecryptApi`'s function as emitted. -/
def cfb8Decrypt : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 984 (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfb8Decrypt)

/-- `Spec.TripleDes.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 984 (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofb)

/-- `Spec.TripleDes.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 984 (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.ofbFinal)

end VG.Impl.TripleDes.X86.Fn
