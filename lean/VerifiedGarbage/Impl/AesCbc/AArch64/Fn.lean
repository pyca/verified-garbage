module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Decrypt
public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# AesCbc on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/AesCbc/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.AesCbc.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64

/-- The vector registers the decryptions leave secrets in. -/
def left : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24,
   .v25, .v26, .v27, .v28, .v29, .v30, .v31]

/-- `codeAes`, then `left` cleared. -/
def decryptAes : Prog isa := withClears [] left none Impl.AesCbc.AArch64.Decrypt.codeAes

/-- `code`, then `left` cleared. -/
def decrypt : Prog isa := withClears [] left none Impl.AesCbc.AArch64.Decrypt.code

end VG.Impl.AesCbc.AArch64.Fn
