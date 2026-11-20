module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Sha512.X86_64.Stream

/-! # Sha512 on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`, or
`scrubAll v rb n` where the residue analysis does not follow the code): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and of the `n` bytes of stack its frames use, the
runs of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs, or all of them, zeroed.
-/

@[expose] public section

namespace VG.Impl.Sha512.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel scrubAll)

/-- `Spec.Sha512.init384Api`'s function as emitted. -/
def init384 : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384)

/-- `Spec.Sha512.init512Api`'s function as emitted. -/
def init512 : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)

/-- `Spec.Sha512.init512_224Api`'s function as emitted. -/
def init512_224 : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224)

/-- `Spec.Sha512.init512_256Api`'s function as emitted. -/
def init512_256 : Prog isa :=
  scrubSel .sse 0 0 []
    (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256)

end VG.Impl.Sha512.X86_64.Fn
