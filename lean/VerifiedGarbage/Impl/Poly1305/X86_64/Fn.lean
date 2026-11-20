module

public import VerifiedGarbage.Impl.Poly1305.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-! # Poly1305 on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Poly1305.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Poly1305.initApi`'s function as emitted. -/
def init : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Poly1305.X86_64.init)

/-- `Spec.Poly1305.finalizeApi`'s function as emitted. -/
def finalize : Prog isa :=
  scrubSel .sse 0 136 []
    (Impl.StackScratch.X86_64.withStackScratch 136 .rcx Impl.Poly1305.X86_64.finalize)

end VG.Impl.Poly1305.X86_64.Fn
