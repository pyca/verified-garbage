module

public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
public import VerifiedGarbage.Impl.TripleDes.AArch64.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.AArch64.Fb
public import VerifiedGarbage.Impl.TripleDes.AArch64.FbFinal
public import VerifiedGarbage.Impl.TripleDes.AArch64.Short
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# TripleDes on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/TripleDes/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.TripleDes.AArch64.Fn

open VG.AArch64
open VG.Impl.Scrub.AArch64

/-- `vg_triple_des_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa :=
  withClears [.x5, .x6, .x8, .x9, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1120 .x4 140 Impl.TripleDes.AArch64.Short.cbcDecryptChained)

/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa :=
  withClears [.x5, .x6, .x9, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 464 .x4 58 Impl.TripleDes.AArch64.TablesCbc.encrypt)

/-- `vg_triple_des_cfb8_decrypt`. -/
def cfb8Decrypt : Prog isa :=
  withClears [.x6, .x7, .x9, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 Impl.TripleDes.AArch64.cfb8Decrypt)

/-- `vg_triple_des_cfb8_encrypt`. -/
def cfb8Encrypt : Prog isa :=
  withClears [.x6, .x7, .x9, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 Impl.TripleDes.AArch64.cfb8Encrypt)

/-- `vg_triple_des_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa :=
  withClears [.x5, .x6, .x8, .x9, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1120 .x4 140 Impl.TripleDes.AArch64.Short.cfb64Decrypt)

/-- `vg_triple_des_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa :=
  withClears [.x6, .x7, .x9, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 Impl.TripleDes.AArch64.cfbDecryptFinal)

/-- `vg_triple_des_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa :=
  withClears [.x6, .x7, .x9, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 Impl.TripleDes.AArch64.cfbEncrypt)

/-- `vg_triple_des_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa :=
  withClears [.x6, .x7, .x9, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 Impl.TripleDes.AArch64.cfbEncryptFinal)

/-- `vg_triple_des_ecb_decrypt`. -/
def ecbDecrypt : Prog isa :=
  withClears [.x5, .x6, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1024 .x3 128 Impl.TripleDes.AArch64.Short.ecbDecrypt)

/-- `vg_triple_des_ecb_encrypt`. -/
def ecbEncrypt : Prog isa :=
  withClears [.x5, .x6, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1024 .x3 128 Impl.TripleDes.AArch64.Short.ecbEncrypt)

/-- `vg_triple_des_ofb`. -/
def ofb : Prog isa :=
  withClears [.x6, .x7, .x9, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 Impl.TripleDes.AArch64.ofb)

/-- `vg_triple_des_ofb_final`. -/
def ofbFinal : Prog isa :=
  withClears [.x6, .x7, .x9, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 Impl.TripleDes.AArch64.ofbFinal)

/-- The key expansion, then what it leaves cleared: words of the key in
`x4`–`x6`, and the key and the subkeys in `v0`–`v7` and `v16`–`v19`. -/
def expandKey : Prog isa :=
  withClears [.x4, .x5, .x6]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19] none Impl.TripleDes.AArch64.Key.expandKey

end VG.Impl.TripleDes.AArch64.Fn
