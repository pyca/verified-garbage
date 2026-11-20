module

public import VerifiedGarbage.Impl.Rc4.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Rc4 on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/Rc4/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.Rc4.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64

def apply : Prog isa :=
  withClearsHi [.x4, .x5, .x6, .x8, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
     .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none .x4 [.v9, .v10, .v11, .v14]
    Impl.Rc4.AArch64.apply

/-- `init`, then what it leaves cleared: the vector registers that held the
table and the key (`v0`–`v7`, `v16`–`v31`), and the high halves of `v8`–`v13`,
whose low halves it restores and which the calling convention does not
preserve, from `x9`, zeroed first. -/
def init : Prog isa :=
  withClearsHi [.x9]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
     .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none .x9 [.v8, .v9, .v10, .v11, .v12, .v13] Impl.Rc4.AArch64.init

end VG.Impl.Rc4.AArch64.Fn
