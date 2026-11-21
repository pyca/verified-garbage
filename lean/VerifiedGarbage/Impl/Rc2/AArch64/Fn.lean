module

public import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
public import VerifiedGarbage.Impl.Rc2.AArch64.Stream
public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Rc2 on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/Rc2/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.Rc2.AArch64.Fn

open VG.AArch64
open VG.Impl.Scrub.AArch64

/-- `vg_rc2_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa :=
  withClears [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 512 .x4 64 Impl.Rc2.AArch64.Cbc.decrypt)

/-- `vg_rc2_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa :=
  withClears [.x3, .x4, .x5, .x6, .x7, .x8]
    [.v0, .v1, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 512 .x4 64 Impl.Rc2.AArch64.Cbc.encrypt)

/-- `vg_rc2_cbc_init`, before its granules [0] are zeroed. -/
def cbcInitBase : Prog isa :=
  withClears [.x3, .x8]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 Impl.Rc2.AArch64.Stream.init)

/-- `vg_rc2_cbc_init`. -/
def cbcInit : Prog isa := scrubSel 592 [0] cbcInitBase

end VG.Impl.Rc2.AArch64.Fn
