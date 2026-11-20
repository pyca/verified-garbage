module

public import VerifiedGarbage.Impl.ChaCha20.PPC64LE.Stream
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# ChaCha20 on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/ChaCha20/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.ChaCha20.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_chacha20_init`, as emitted. -/
def init : Prog isa :=
  scrub 0 0 ⟨false, false, [.r4, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.ChaCha20.PPC64LE.Stream.init)

/-- `vg_chacha20_set_nonce`, as emitted. -/
def setNonce : Prog isa :=
  scrub 0 0 ⟨false, false, [.r9, .r10, .r11, .r12], false, []⟩
    (Impl.ChaCha20.PPC64LE.Stream.setNonce)

/-- `vg_chacha20_apply`, as emitted. -/
def apply : Prog isa :=
  scrub 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (Impl.ChaCha20.PPC64LE.Stream.apply)

end VG.Impl.ChaCha20.PPC64LE.Fn
