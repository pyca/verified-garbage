module

public import VerifiedGarbage.Impl.Idea.X86
public import VerifiedGarbage.Impl.Idea.X86.Modes
public import VerifiedGarbage.Impl.Idea.X86.FbFinal
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-! # IDEA on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubF rb W`, or
`Impl.Scrub.X86.scrub rb` for code without a frame or calls): the `W` bytes
of stack below `esp` that its contract reserves zeroed, and the registers
a callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Idea.X86.Fn

open VG.X86

/-- `Spec.Idea.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  Impl.Scrub.X86.scrub 0 (Impl.Idea.X86.expandKey)

/-- `Spec.Idea.invertKeyApi`'s function as emitted. -/
def invertKey : Prog isa :=
  Impl.Scrub.X86.scrubF 0 32 (Impl.StackScratch.X86.withStackScratch 32 2 Impl.Idea.X86.invertKey)

/-- `Spec.Idea.ecbApi`'s function as emitted. -/
def ecb : Prog isa :=
  Impl.Scrub.X86.scrubF 0 152 (Impl.StackScratch.X86.withStackScratchWiped 152 3 27 Impl.Idea.X86.ecb)

/-- `Spec.Idea.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubF 0 208 (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cbcEncryptChained)

/-- `Spec.Idea.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubF 0 208 (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cbcDecryptChained)

/-- `Spec.Idea.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  Impl.Scrub.X86.scrubF 0 208 (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbEncrypt)

/-- `Spec.Idea.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  Impl.Scrub.X86.scrubF 0 208 (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbDecrypt)

/-- `Spec.Idea.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubF 0 208 (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbEncryptFinal)

/-- `Spec.Idea.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  Impl.Scrub.X86.scrubF 0 208 (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.cfbDecryptFinal)

/-- `Spec.Idea.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  Impl.Scrub.X86.scrubF 0 208 (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.ofb)

/-- `Spec.Idea.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  Impl.Scrub.X86.scrubF 0 208 (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 Impl.Idea.X86.ofbFinal)

end VG.Impl.Idea.X86.Fn
