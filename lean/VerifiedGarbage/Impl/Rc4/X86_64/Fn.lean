module

public import VerifiedGarbage.Impl.Rc4.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # Rc4 on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Rc4.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Rc4.initApi`'s function as emitted. -/
def init : Prog isa :=
  scrubSel .sse 32 0 []
    (Impl.Rc4.X86_64.init)

/-- `Spec.Rc4.applyApi`'s function as emitted. -/
def apply : Prog isa :=
  scrubAll .sse 0 0
    (Impl.Rc4.X86_64.apply)

end VG.Impl.Rc4.X86_64.Fn
