module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Sha256.X86_64.Stream

/-! # Sha256 on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Sha256.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Sha256.initApi`'s function as emitted. -/
def init : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Sha256.X86_64.Stream.init)

/-- `Spec.Sha256.init224Api`'s function as emitted. -/
def init224 : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Sha256.X86_64.Stream.init224)

end VG.Impl.Sha256.X86_64.Fn
