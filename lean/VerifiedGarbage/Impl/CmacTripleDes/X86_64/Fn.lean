module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-! # CmacTripleDes on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.CmacTripleDes.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Cmac.tdesStreamInitApi`'s function as emitted. -/
def init : Prog isa :=
  scrubSel .sse 0 128 [(0, 1), (8, 8)]
    (Impl.StackScratch.X86_64.withStackScratch 128 .rcx Impl.CmacTripleDes.Stream.X86_64.streamInit)

/-- `Spec.Cmac.tdesAbsorbApi`'s function as emitted. -/
def absorb : Prog isa :=
  scrubSel .sse 0 168 [(0, 11)]
    (Impl.StackScratch.X86_64.withStackScratch 168 .r8 Impl.CmacTripleDes.Stream.X86_64.absorb)

/-- `Spec.Cmac.tdesFinishApi`'s function as emitted. -/
def finish : Prog isa :=
  scrubSel .sse 0 128 [(0, 1), (8, 8)]
    (Impl.StackScratch.X86_64.withStackScratch 128 .rcx Impl.CmacTripleDes.Stream.X86_64.finish)

end VG.Impl.CmacTripleDes.X86_64.Fn
