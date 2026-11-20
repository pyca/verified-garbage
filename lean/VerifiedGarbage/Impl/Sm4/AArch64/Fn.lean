module

public import VerifiedGarbage.Impl.Modes.FbMode
public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub
public import VerifiedGarbage.Impl.Sm4.AArch64.Cbc
public import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
public import VerifiedGarbage.Impl.Sm4.AArch64.EcbFew
public import VerifiedGarbage.Impl.Sm4.AArch64.Fb
public import VerifiedGarbage.Impl.Sm4.AArch64.FbFinal
public import VerifiedGarbage.Impl.Sm4.AArch64.Sm4e.Ecb
public import VerifiedGarbage.Impl.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Spec.Sm4
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Sm4 on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/Sm4/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64

/-- `vg_sm4_ecb`'s code: `ecbAny` with its working space on the stack. -/
def ecbAnyFramed : Prog isa := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 Impl.Sm4.AArch64.ecbAny

/-- `vg_sm4_ecb_decrypt`, before its granules [0, 1, 2, 3, 4, 203] are zeroed. -/
def ecbDecryptBase : Prog isa :=
  withClears [.x6, .x7, .x8, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30] none
    (Impl.Sm4.AArch64.ecbFew .decrypt ecbAnyFramed)

/-- `vg_sm4_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := withScrubG 3264 [0, 1, 2, 3, 4, 203] ecbDecryptBase

/-- `vg_sm4_ecb_encrypt`, before its granules [0, 1, 2, 3, 4, 203] are zeroed. -/
def ecbEncryptBase : Prog isa :=
  withClears [.x6, .x7, .x8, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30] none
    (Impl.Sm4.AArch64.ecbFew .encrypt ecbAnyFramed)

/-- `vg_sm4_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := withScrubG 3264 [0, 1, 2, 3, 4, 203] ecbEncryptBase

/-- `vg_sm4_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cbcDecryptChained)

/-- `vg_sm4_cbc_decrypt_chained_sm4`. -/
def cbcDecryptChainedSm4 : Prog isa :=
  withClears [.x6, .x8, .x9]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Sm4.AArch64.Sm4e.cbcDecryptChained)

/-- `vg_sm4_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cbcEncryptChained)

/-- `vg_sm4_cbc_encrypt_chained_sm4`. -/
def cbcEncryptChainedSm4 : Prog isa :=
  withClears [.x6, .x7]
    [.v0, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 Impl.Sm4.AArch64.Sm4e.cbcEncryptChained)

/-- `vg_sm4_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cfbDecrypt)

/-- `vg_sm4_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa :=
  withClears [.x6, .x7, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cfbDecryptFinal)

/-- `vg_sm4_cfb128_decrypt_final_sm4`. -/
def cfbDecryptFinalSm4 : Prog isa :=
  withClears [.x6, .x7]
    [.v0, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 (Impl.Sm4.AArch64.Sm4e.fbFinal .cfbDec))

/-- `vg_sm4_cfb128_decrypt_sm4`. -/
def cfbDecryptSm4 : Prog isa :=
  withClears [.x6, .x8, .x9]
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Sm4.AArch64.Sm4e.cfbDecrypt)

/-- `vg_sm4_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cfbEncrypt)

/-- `vg_sm4_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa :=
  withClears [.x6, .x7, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.cfbEncryptFinal)

/-- `vg_sm4_cfb128_encrypt_final_sm4`. -/
def cfbEncryptFinalSm4 : Prog isa :=
  withClears [.x6, .x7]
    [.v0, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 (Impl.Sm4.AArch64.Sm4e.fbFinal .cfbEnc))

/-- `vg_sm4_cfb128_encrypt_sm4`. -/
def cfbEncryptSm4 : Prog isa :=
  withClears [.x6, .x7]
    [.v0, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 (Impl.Sm4.AArch64.Sm4e.fb .cfbEnc))

/-- `vg_sm4_ofb`. -/
def ofb : Prog isa :=
  withClears [.x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.ofb)

/-- `vg_sm4_ofb_final`. -/
def ofbFinal : Prog isa :=
  withClears [.x6, .x7, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.ofbFinal)

/-- `vg_sm4_ofb_final_sm4`. -/
def ofbFinalSm4 : Prog isa :=
  withClears [.x6, .x7]
    [.v0, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 (Impl.Sm4.AArch64.Sm4e.fbFinal .ofb))

/-- `vg_sm4_ofb_sm4`. -/
def ofbSm4 : Prog isa :=
  withClears [.x6, .x7]
    [.v0, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 (Impl.Sm4.AArch64.Sm4e.fb .ofb))

/-- The vector registers `ecb` leaves secrets in. -/
def ecbLeft : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23]

/-- `ecb dir`, then `ecbLeft` cleared. -/
def ecb (dir : Impl.Sm4.AArch64.Dir) : Prog isa := withClears [] ecbLeft none (Impl.Sm4.AArch64.Sm4e.ecb dir)

end VG.Impl.Sm4.AArch64.Fn
