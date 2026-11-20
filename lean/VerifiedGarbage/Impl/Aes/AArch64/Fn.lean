module

public import VerifiedGarbage.Impl.Aes.AArch64.Aese
public import VerifiedGarbage.Impl.Aes.AArch64.ExpandKey
public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Aes on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/Aes/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.Aes.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64

/-- `vg_aes_expand_key_aes`. -/
def expandKeyAes : Prog isa :=
  withClears [.x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13]
    [.v1] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 512 .x3 64 Impl.Aes.AArch64.Aese.expandKey)

/-- `vg_aes_expand_key`. -/
def expandKey : Prog isa :=
  withClears [.x6, .x8]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 512 .x3 64 Impl.Aes.AArch64.expandKey)

end VG.Impl.Aes.AArch64.Fn
