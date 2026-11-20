module

public import VerifiedGarbage.Impl.Blake2.X86_64.Stream
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # Blake2 on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Blake2.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Blake2.initBApi`'s function as emitted. -/
def initB : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b)

/-- `Spec.Blake2.initSApi`'s function as emitted. -/
def initS : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Blake2.X86_64.Stream.init Spec.Blake2.s)

end VG.Impl.Blake2.X86_64.Fn
