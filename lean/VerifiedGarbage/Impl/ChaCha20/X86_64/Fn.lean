module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.Stream
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # ChaCha20 on x86-64: the functions as emitted

`vg_chacha20_init`, `vg_chacha20_set_nonce` and, generic over the
implementation of `vg_chacha20_xor` it calls, `vg_chacha20_apply`, each
followed by its cleanup (`Impl.Scrub.X86_64.scrubAll v rb n`): every vector
register at the level `v` and every caller-saved register but the `rb` bits
of the result cleared, and the `n` bytes of stack its calls use wiped.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.ChaCha20.initApi`'s function as emitted. -/
def init : Prog isa := scrubAll .sse 0 0 Impl.ChaCha20.X86_64.Stream.init

/-- `Spec.ChaCha20.setNonceApi`'s function as emitted. -/
def setNonce : Prog isa := scrubAll .sse 0 0 Impl.ChaCha20.X86_64.Stream.setNonce

/-- `Spec.ChaCha20.applyApi`'s function as emitted over `x`, its cleanup at
the level `v`. -/
def apply (v : VecLevel) (x : Impl.ChaCha20.X86_64.Callee) : Prog isa :=
  scrubAll v 32 24 (Impl.ChaCha20.X86_64.Stream.apply x)

end VG.Impl.ChaCha20.X86_64.Fn
