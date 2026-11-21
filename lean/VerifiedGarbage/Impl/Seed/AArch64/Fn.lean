module

public import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.Seed.AArch64.ExpandKey
public import VerifiedGarbage.Impl.Seed.AArch64.FbFinal
public import VerifiedGarbage.Impl.Seed.AArch64.Modes
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Seed on AArch64: the functions as emitted

Each function is its code, then its cleanup: the registers it leaves secrets
in are cleared and, where it leaves any there, its stack is zeroed, so that
it returns without secret residue (`Proof/Seed/AArch64/`).
-/

@[expose] public section

namespace VG.Impl.Seed.AArch64.Fn

open VG.AArch64
open VG.Impl.Scrub.AArch64

/-- `vg_seed_ecb_decrypt`, before its granules [0] are zeroed. -/
def ecbDecryptBase : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x14]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x3 182 Impl.Seed.AArch64.ecbDecrypt))

/-- `vg_seed_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubSel 1472 [0] ecbDecryptBase

/-- `vg_seed_ecb_encrypt`, before its granules [0] are zeroed. -/
def ecbEncryptBase : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x14]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x3 182 Impl.Seed.AArch64.ecbEncrypt))

/-- `vg_seed_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrubSel 1472 [0] ecbEncryptBase

/-- `vg_seed_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x9, .x10, .x11, .x12]
    [.v0, .v1, .v3, .v27, .v28, .v29, .v30] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcDecryptChained))

/-- `vg_seed_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cbcEncryptChained))

/-- `vg_seed_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3, .v27, .v28, .v29, .v30] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbDecrypt))

/-- `vg_seed_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbDecryptFinal))

/-- `vg_seed_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbEncrypt))

/-- `vg_seed_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbEncryptFinal))

/-- `vg_seed_expand_key`. -/
def expandKey : Prog isa :=
  withClears [.x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14]
    [] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 976 .x2 122 Impl.Seed.AArch64.expandKey)

/-- `vg_seed_ofb`. -/
def ofb : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.ofb))

/-- `vg_seed_ofb_final`. -/
def ofbFinal : Prog isa :=
  withRet 0 (withClears [.x1, .x2, .x3, .x6, .x7, .x9, .x10, .x11, .x12, .x13]
    [.v0, .v1, .v3] none
    (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.ofbFinal))

end VG.Impl.Seed.AArch64.Fn
