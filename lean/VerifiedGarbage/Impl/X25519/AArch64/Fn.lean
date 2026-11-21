module

public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.X25519.AArch64.AltLadder
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
  withRet 32 (withClears [.x3, .x4, .x5, .x6, .x7, .x8, .x10, .x12, .x13, .x14, .x15, .x16, .x17]
    [] (some .x3)
    (Impl.Xdh.AArch64.exchange "vg_x25519" Impl.X25519.AArch64.AltLadder.x25519 32))

/-- `vg_x25519_exchange`. -/
def exchange : Prog isa := scrubSel 16 [0] exchangeBase

end VG.Impl.X25519.AArch64.Fn
