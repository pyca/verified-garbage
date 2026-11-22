module

public import VerifiedGarbage.Impl.Aes.Arm.ExpandKey
public import VerifiedGarbage.Impl.AesEcb.Arm
public import VerifiedGarbage.Impl.AesCbc.Arm.Wiped
public import VerifiedGarbage.Impl.AesCtr.Arm
public import VerifiedGarbage.Impl.AesCtr.Arm.Final
public import VerifiedGarbage.Impl.AesCfb.Arm
public import VerifiedGarbage.Impl.AesCfb.Arm.Final
public import VerifiedGarbage.Impl.AesCfb8.Arm
public import VerifiedGarbage.Impl.AesOfb.Arm
public import VerifiedGarbage.Impl.AesOfb.Arm.Final
public import VerifiedGarbage.Impl.AesXts.ArmUnit
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# AES and its modes on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Scrub/Arm.lean`,
`scrubAll`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change, set to constants.
`Proof/Aes/Arm/Scrub.lean` states that each returns without secret residue.

The `_final` functions of CTR, CFB128 and OFB call the code of the
whole-block ones without the cleanup, under names of their own
(`vg_aes_ctr_entry`, …), which the emitter writes as internal functions:
their own cleanup covers the frames of that call.
-/

@[expose] public section

namespace VG.Impl.Aes.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm VG.Impl.StackScratch.Arm

/-- `vg_aes_expand_key`. -/
def expandKey : Prog isa := scrubAll 0 512 (withRegScratch 512 .r3 Impl.Aes.Arm.expandKey)

/-- `vg_aes_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrubAll 0 24 Impl.AesEcb.Arm.encrypt

/-- `vg_aes_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubAll 0 24 Impl.AesEcb.Arm.decrypt

/-- `vg_aes_cbc_encrypt`. -/
def cbcEncrypt : Prog isa := scrubAll 0 32 Impl.AesCbc.Arm.Wiped.encrypt

/-- `vg_aes_cbc_decrypt`. -/
def cbcDecrypt : Prog isa := scrubAll 0 32 Impl.AesCbc.Arm.Wiped.decrypt

/-- `vg_aes_ctr`. -/
def ctr : Prog isa := scrubAll 0 8 Impl.AesCtr.Arm.crypt

/-- `vg_aes_ctr_final`. -/
def ctrFinal : Prog isa := scrubAll 0 88 (withStackScratch 72 2 Impl.AesCtr.Arm.cryptFinal)

/-- `vg_aes_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := scrubAll 0 8 Impl.AesCfb.Arm.encrypt

/-- `vg_aes_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := scrubAll 0 8 Impl.AesCfb.Arm.decrypt

/-- `vg_aes_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubAll 0 72 (withStackScratch 56 2 Impl.AesCfb.Arm.encryptFinal)

/-- `vg_aes_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubAll 0 72 (withStackScratch 56 2 Impl.AesCfb.Arm.decryptFinal)

/-- `vg_aes_cfb8_encrypt`. -/
def cfb8Encrypt : Prog isa := scrubAll 0 8 Impl.AesCfb8.Arm.encrypt

/-- `vg_aes_cfb8_decrypt`. -/
def cfb8Decrypt : Prog isa := scrubAll 0 8 Impl.AesCfb8.Arm.decrypt

/-- `vg_aes_ofb`. -/
def ofb : Prog isa := scrubAll 0 8 Impl.AesOfb.Arm.crypt

/-- `vg_aes_ofb_final`. -/
def ofbFinal : Prog isa := scrubAll 0 72 (withStackScratch 56 2 Impl.AesOfb.Arm.cryptFinal)

/-- `vg_aes_xts_encrypt_unit`. -/
def xtsEncrypt : Prog isa := scrubAll 0 16 Impl.AesXts.ArmUnit.encrypt

/-- `vg_aes_xts_decrypt_unit`. -/
def xtsDecrypt : Prog isa := scrubAll 0 16 Impl.AesXts.ArmUnit.decrypt

end VG.Impl.Aes.Arm.Fn
