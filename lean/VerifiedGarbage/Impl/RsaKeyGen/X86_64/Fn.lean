module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.KeyInit

/-! # RSA key generation on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubAll v rb n`): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and the `n` bytes of stack its frames use zeroed.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `Spec.RsaKeyGen.keyInitApi`'s function as emitted. -/
def keyInit : Prog isa := scrubAll .sse 32 0 KeyInit.init

end VG.Impl.RsaKeyGen.X86_64.Fn
