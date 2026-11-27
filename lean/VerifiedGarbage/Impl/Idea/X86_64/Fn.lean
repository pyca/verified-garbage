module

public import VerifiedGarbage.Impl.Idea.X86_64
public import VerifiedGarbage.Impl.Idea.X86_64.FbFinal
public import VerifiedGarbage.Impl.Idea.X86_64.Modes
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-! # Idea on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Idea.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Idea.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Idea.X86_64.expandKey)

/-- `Spec.Idea.invertKeyApi`'s function as emitted. -/
def invertKey : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Idea.X86_64.invertKey)

/-- `Spec.Idea.ecbApi`'s function as emitted. -/
def ecb : Prog isa :=
  scrubSel .sse 0 24 [(0, 2)]
    (Impl.StackScratch.X86_64.withStackScratch 24 .rcx Impl.Idea.X86_64.ecb)

/-- `Spec.Idea.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncrypt : Prog isa :=
  scrubSel .sse 0 184 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cbcEncryptChained)

/-- `Spec.Idea.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecrypt : Prog isa :=
  scrubSel .sse 0 184 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cbcDecryptChained)

/-- `Spec.Idea.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubSel .sse 0 184 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbEncrypt)

/-- `Spec.Idea.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubSel .sse 0 184 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbDecrypt)

/-- `Spec.Idea.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubSel .sse 0 184 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbEncryptFinal)

/-- `Spec.Idea.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubSel .sse 0 184 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cfbDecryptFinal)

/-- `Spec.Idea.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrubSel .sse 0 184 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.ofb)

/-- `Spec.Idea.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrubSel .sse 0 184 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.ofbFinal)

end VG.Impl.Idea.X86_64.Fn
