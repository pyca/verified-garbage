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
public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Impl.Residue.ArmSel

/-!
# AES and its modes on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Residue/Arm.lean`,
`scrubF`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change, set to constants. Key expansion
wipes its own working space, and its cleanup zeroes only the words of that
stack that the residue analysis (`Arm.rtaint`) finds may differ between two
runs (`Impl/Residue/ArmSel.lean`, `scrubSel`): none. `Proof/Aes/Arm/Scrub.lean` states that each returns without
secret residue.

The `_final` functions of CTR, CFB128 and OFB call the code of the
whole-block ones without the cleanup, under names of their own
(`vg_aes_ctr_entry`, …), which the emitter writes as internal functions:
their own cleanup covers the frames of that call.
-/

@[expose] public section

namespace VG.Impl.Aes.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm VG.Impl.StackScratch.Arm

/-- The words key expansion leaves secret: none. -/
def expandKeyWords : List Nat := []

/-- `vg_aes_expand_key`. -/
def expandKey : Prog isa := scrubSel 0 512 expandKeyWords (withRegScratchWiped 512 .r3 128 Impl.Aes.Arm.expandKey)

/-- `vg_aes_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrubF 0 24 Impl.AesEcb.Arm.encrypt

/-- `vg_aes_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubF 0 24 Impl.AesEcb.Arm.decrypt

/-- `vg_aes_cbc_encrypt`. -/
def cbcEncrypt : Prog isa := scrubF 0 32 Impl.AesCbc.Arm.Wiped.encrypt

/-- `vg_aes_cbc_decrypt`. -/
def cbcDecrypt : Prog isa := scrubF 0 32 Impl.AesCbc.Arm.Wiped.decrypt

/-- `vg_aes_ctr`. -/
def ctr : Prog isa := scrubF 0 8 Impl.AesCtr.Arm.crypt

/-- `vg_aes_ctr_final`. -/
def ctrFinal : Prog isa := scrubF 0 88 (withStackScratchWiped 72 2 14 Impl.AesCtr.Arm.cryptFinal)

/-- `vg_aes_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := scrubF 0 8 Impl.AesCfb.Arm.encrypt

/-- `vg_aes_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := scrubF 0 8 Impl.AesCfb.Arm.decrypt

/-- `vg_aes_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubF 0 72 (withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.encryptFinal)

/-- `vg_aes_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubF 0 72 (withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.decryptFinal)

/-- `vg_aes_cfb8_encrypt`. -/
def cfb8Encrypt : Prog isa := scrubF 0 8 Impl.AesCfb8.Arm.encrypt

/-- `vg_aes_cfb8_decrypt`. -/
def cfb8Decrypt : Prog isa := scrubF 0 8 Impl.AesCfb8.Arm.decrypt

/-- `vg_aes_ofb`. -/
def ofb : Prog isa := scrubF 0 8 Impl.AesOfb.Arm.crypt

/-- `vg_aes_ofb_final`. -/
def ofbFinal : Prog isa := scrubF 0 72 (withStackScratchWiped 56 2 10 Impl.AesOfb.Arm.cryptFinal)

/-- `vg_aes_xts_encrypt_unit`. -/
def xtsEncrypt : Prog isa := scrubF 0 16 Impl.AesXts.ArmUnit.encrypt

/-- `vg_aes_xts_decrypt_unit`. -/
def xtsDecrypt : Prog isa := scrubF 0 16 Impl.AesXts.ArmUnit.decrypt

end VG.Impl.Aes.Arm.Fn
