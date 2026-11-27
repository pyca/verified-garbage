module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Seed.X86_64.ExpandKey
public import VerifiedGarbage.Impl.Seed.X86_64.FbFinal
public import VerifiedGarbage.Impl.Seed.X86_64.Modes
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-! # Seed on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Seed.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Seed.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrubSel .sse 0 1064 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rdx 132 Impl.Seed.X86_64.expandKey)

/-- `Spec.Seed.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubSel .sse 0 1104 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .encrypt))

/-- `Spec.Seed.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubSel .sse 0 1104 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .decrypt))

/-- `Spec.Seed.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncrypt : Prog isa :=
  scrubSel .sse 0 1552 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cbcEncryptChained)

/-- `Spec.Seed.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecrypt : Prog isa :=
  scrubSel .sse 0 1552 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cbcDecryptChained)

/-- `Spec.Seed.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubSel .sse 0 1552 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbEncrypt)

/-- `Spec.Seed.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubSel .sse 0 1552 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbEncryptFinal)

/-- `Spec.Seed.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubSel .sse 0 1552 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbDecrypt)

/-- `Spec.Seed.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubSel .sse 0 1552 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbDecryptFinal)

/-- `Spec.Seed.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrubSel .sse 0 1552 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.ofb)

/-- `Spec.Seed.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrubSel .sse 0 1552 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.ofbFinal)

end VG.Impl.Seed.X86_64.Fn
