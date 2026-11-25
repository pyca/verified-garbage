module

public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.X25519.AArch64.Ladder
public import VerifiedGarbage.Impl.X25519.AArch64.Base
public import VerifiedGarbage.Impl.Xdh.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# X25519 on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/X25519/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.X25519.AArch64.Fn

open VG.AArch64
open VG.Impl.Scrub.AArch64

def x25519Base : Prog isa :=
  withClears
    [.x1, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17] [] (some .x1)
    Impl.X25519.AArch64.Base.x25519Base

/-- `vg_x25519_exchange`, before its granules [0] are zeroed. -/
def exchangeBase : Prog isa :=
  withRet 32 (withClearsHi [.x3, .x4, .x5, .x6, .x7, .x8, .x10, .x12, .x13, .x14, .x15, .x16, .x17]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
      .v27, .v28, .v29, .v30, .v31] (some .x3) .x3 [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]
    (Impl.Xdh.AArch64.exchange "vg_x25519" Impl.X25519.AArch64.Ladder.x25519 32))

/-- `vg_x25519_exchange`. -/
def exchange : Prog isa := scrubSel 16 [0] exchangeBase

end VG.Impl.X25519.AArch64.Fn
