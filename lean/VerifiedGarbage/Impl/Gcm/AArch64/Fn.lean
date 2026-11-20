module

public import VerifiedGarbage.Impl.Gcm.AArch64.Pmull
public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Gcm on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/Gcm/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.Gcm.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64

/-- `keyPowers`, then the powers of the hash key it leaves in `v3`–`v7` and
`v16`–`v31` cleared. -/
def keyPowers : Prog isa :=
  withClears []
    [.v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
     .v27, .v28, .v29, .v30, .v31] none Impl.Gcm.AArch64.Pmull.keyPowers

end VG.Impl.Gcm.AArch64.Fn
