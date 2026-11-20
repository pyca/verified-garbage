module

public import VerifiedGarbage.Impl.Rc2.X86.Stream
public import VerifiedGarbage.Impl.Rc2.X86.Cbc
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-! # RC2 on x86 (32-bit): the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubF rb W`, or
`Impl.Scrub.X86.scrub rb` for code without a frame or calls): the `W` bytes
of stack below `esp` that its contract reserves zeroed, and the registers
a callee may change cleared but the `rb` bits of the result, so that it
returns without secret residue. -/

@[expose] public section

namespace VG.Impl.Rc2.X86.Fn

open VG.X86

/-- `Spec.Rc2.cbcInitApi`'s function as emitted. -/
def cbcInit : Prog isa :=
  Impl.Scrub.X86.scrubF 32 632 (Impl.StackScratch.X86.withStackScratch 608 6 Impl.Rc2.X86.Stream.init)

/-- `Spec.Rc2.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  Impl.Scrub.X86.scrubF 0 560 (Impl.StackScratch.X86.withStackScratch 544 4 Impl.Rc2.X86.Cbc.encrypt)

/-- `Spec.Rc2.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  Impl.Scrub.X86.scrubF 0 560 (Impl.StackScratch.X86.withStackScratch 544 4 Impl.Rc2.X86.Cbc.decrypt)

end VG.Impl.Rc2.X86.Fn
