module

public import VerifiedGarbage.Impl.ChaCha20.RISCV64.Stream
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# ChaCha20 on RISC-V, as emitted

`vg_chacha20_init`, `vg_chacha20_set_nonce` and `vg_chacha20_apply`, each
followed by its cleanup (`Impl.Scrub.RISCV64.scrub`): the caller-saved
registers cleared but the result's bits (none, none, 32); they use no stack.
In a module of its own, so that what imports their code (ChaCha20-Poly1305)
does not import their cleanup.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.RISCV64.Fn

open VG.RISCV64 VG.Impl.Scrub.RISCV64

/-- `vg_chacha20_init`, then its cleanup. -/
def init : Prog isa := scrub 0 0 Impl.ChaCha20.RISCV64.Stream.init

/-- `vg_chacha20_set_nonce`, then its cleanup. -/
def setNonce : Prog isa := scrub 0 0 Impl.ChaCha20.RISCV64.Stream.setNonce

/-- `vg_chacha20_apply`, then its cleanup. -/
def apply : Prog isa := scrub 32 0 Impl.ChaCha20.RISCV64.Stream.apply

end VG.Impl.ChaCha20.RISCV64.Fn
