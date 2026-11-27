module

public import VerifiedGarbage.Impl.Blowfish.X86_64
public import VerifiedGarbage.Impl.Blowfish.X86_64.FbFinal
public import VerifiedGarbage.Impl.Blowfish.X86_64.Modes
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-! # Blowfish on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Blowfish.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Blowfish.expandKeyApi`'s function as emitted. -/
def expandKey : Prog isa :=
  scrubSel .sse 0 40 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 40 .rcx 4 Impl.Blowfish.X86_64.expandKey)

/-- `Spec.Blowfish.ecbEncryptApi`'s function as emitted. -/
def ecbEncrypt : Prog isa :=
  scrubSel .sse 0 264 [(0, 17)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 Impl.Blowfish.X86_64.encrypt)

/-- `Spec.Blowfish.ecbDecryptApi`'s function as emitted. -/
def ecbDecrypt : Prog isa :=
  scrubSel .sse 0 264 [(0, 17)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 Impl.Blowfish.X86_64.decrypt)

/-- `Spec.Blowfish.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncrypt : Prog isa :=
  scrubSel .sse 0 96 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcEncryptChained)

/-- `Spec.Blowfish.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecrypt : Prog isa :=
  scrubSel .sse 0 96 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcDecryptChained)

/-- `Spec.Blowfish.cfbEncryptApi`'s function as emitted. -/
def cfbEncrypt : Prog isa :=
  scrubSel .sse 0 96 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbEncrypt)

/-- `Spec.Blowfish.cfbDecryptApi`'s function as emitted. -/
def cfbDecrypt : Prog isa :=
  scrubSel .sse 0 96 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbDecrypt)

/-- `Spec.Blowfish.cfbEncryptFinalApi`'s function as emitted. -/
def cfbEncryptFinal : Prog isa :=
  scrubSel .sse 0 96 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbEncryptFinal)

/-- `Spec.Blowfish.cfbDecryptFinalApi`'s function as emitted. -/
def cfbDecryptFinal : Prog isa :=
  scrubSel .sse 0 96 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbDecryptFinal)

/-- `Spec.Blowfish.ofbApi`'s function as emitted. -/
def ofb : Prog isa :=
  scrubSel .sse 0 96 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.ofb)

/-- `Spec.Blowfish.ofbFinalApi`'s function as emitted. -/
def ofbFinal : Prog isa :=
  scrubSel .sse 0 96 [(0, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.ofbFinal)

end VG.Impl.Blowfish.X86_64.Fn
