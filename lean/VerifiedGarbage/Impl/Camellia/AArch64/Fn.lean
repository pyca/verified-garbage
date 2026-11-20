module

public import VerifiedGarbage.Impl.Camellia.AArch64.Cbc
public import VerifiedGarbage.Impl.Camellia.AArch64.Ecb
public import VerifiedGarbage.Impl.Camellia.AArch64.ExpandKey
public import VerifiedGarbage.Impl.Camellia.AArch64.Fb
public import VerifiedGarbage.Impl.Camellia.AArch64.FbFinal
public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Camellia on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/Camellia/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64

/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cbcDecryptChained)

/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa :=
  withClears [.x6, .x7, .x8, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cbcEncryptChained)

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbDecrypt)

/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa :=
  withClears [.x6, .x7, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbDecryptFinal)

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa :=
  withClears [.x6, .x7, .x8, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbEncrypt)

/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa :=
  withClears [.x6, .x7, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.cfbEncryptFinal)

/-- `vg_camellia_ecb_decrypt`. -/
def ecbDecrypt : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x4 406 (Impl.Camellia.AArch64.ecb .decrypt))

/-- `vg_camellia_ecb_encrypt`. -/
def ecbEncrypt : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x4 406 (Impl.Camellia.AArch64.ecb .encrypt))

/-- `vg_camellia_expand_key`. -/
def expandKey : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 160 .x3 20 Impl.Camellia.AArch64.expandKey)

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa :=
  withClears [.x6, .x7, .x8, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.ofb)

/-- `vg_camellia_ofb_final`. -/
def ofbFinal : Prog isa :=
  withClears [.x6, .x7, .x10, .x11, .x12]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 Impl.Camellia.AArch64.ofbFinal)

end VG.Impl.Camellia.AArch64.Fn
