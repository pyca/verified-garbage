module

public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.X448.AArch64.Field56
public import VerifiedGarbage.Impl.Xdh.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# X448 on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/X448/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.X448.AArch64.Fn

open VG.AArch64
open VG.Impl.Scrub.AArch64

/-- `vg_x448_exchange`, before its granules [0] are zeroed. -/
def exchangeBase : Prog isa :=
  withRet 32 (withClearsHi [.x2, .x4, .x5, .x6, .x7, .x8, .x10, .x13, .x14, .x15, .x16, .x17]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v19, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29] (some .x2) .x2 [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]
    (Impl.Xdh.AArch64.exchange "vg_x448" Impl.X448.AArch64.Fast.x448 56))

/-- `vg_x448_exchange`. -/
def exchange : Prog isa := scrubSel 16 [0] exchangeBase

end VG.Impl.X448.AArch64.Fn
