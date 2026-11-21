module

public import VerifiedGarbage.Impl.Cast5.X86_64
public import VerifiedGarbage.Impl.Cast5.X86_64.FbFinal
public import VerifiedGarbage.Impl.Cast5.X86_64.Modes
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-! # Cast5 on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Cast5.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Cast5.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrubAll .sse 0 0
    (Impl.Cast5.X86_64.expandKey)

/-- `Spec.Cast5.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubAll .sse 0 0
    (Impl.Cast5.X86_64.ecbEncrypt)

/-- `Spec.Cast5.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubAll .sse 0 0
    (Impl.Cast5.X86_64.ecbDecrypt)

/-- `Spec.Cast5.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrubAll .sse 0 240
    (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cbcEncryptChained)

/-- `Spec.Cast5.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrubAll .sse 0 240
    (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cbcDecryptChained)

/-- `Spec.Cast5.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubAll .sse 0 240
    (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbEncrypt)

/-- `Spec.Cast5.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubAll .sse 0 240
    (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbDecrypt)

/-- `Spec.Cast5.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubAll .sse 0 240
    (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbEncryptFinal)

/-- `Spec.Cast5.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubAll .sse 0 240
    (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbDecryptFinal)

/-- `Spec.Cast5.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrubAll .sse 0 240
    (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.ofb)

/-- `Spec.Cast5.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrubAll .sse 0 240
    (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.ofbFinal)

end VG.Impl.Cast5.X86_64.Fn
