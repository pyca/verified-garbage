module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Zeroize.X86_64

/-! # Zeroize on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Zeroize.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Zeroize.zeroizeApi`'s function as emitted. -/
def zeroize : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Zeroize.X86_64.zeroize)

/-- `Spec.Zeroize.zeroizeApi`'s function (`_avx`) as emitted. -/
def zeroizeAvx : Prog isa :=
  scrubSel .avx 0 0 []
    (Impl.Zeroize.X86_64.zeroizeAvx)

end VG.Impl.Zeroize.X86_64.Fn
