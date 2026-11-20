module

public import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
public import VerifiedGarbage.Impl.Rc2.X86_64.Stream
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-! # RC2 on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubSel v rb n rs`):
every SSE register and every caller-saved register but the `rb` bits of the
result cleared, and of the `n` bytes of stack its frames use, only the runs
of granules `rs` that the residue analysis (`X86_64.RTaint`) finds may
differ between two runs zeroed.
-/

@[expose] public section

namespace VG.Impl.Rc2.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubSel)

/-- `Spec.Rc2.cbcInitApi`'s function as emitted. -/
def cbcInit : Prog isa :=
  scrubSel .sse 32 600 [(0, 2)]
    (Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72 Impl.Rc2.X86_64.Stream.init)

/-- `Spec.Rc2.cbcEncryptChainedApi`'s function as emitted. -/
def cbcEncryptChained : Prog isa :=
  scrubSel .sse 0 528 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 520 .r8 64 Impl.Rc2.X86_64.Cbc.encrypt)

/-- `Spec.Rc2.cbcDecryptChainedApi`'s function as emitted. -/
def cbcDecryptChained : Prog isa :=
  scrubSel .sse 0 528 [(8, 1)]
    (Impl.StackScratch.X86_64.withStackScratchWiped 520 .r8 64 Impl.Rc2.X86_64.Cbc.decrypt)

end VG.Impl.Rc2.X86_64.Fn
