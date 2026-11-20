module

public import VerifiedGarbage.Impl.Blowfish.Arm.FbFinal
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Impl.Residue.ArmSel

/-!
# Blowfish's functions on ARMv7, as emitted

Each is its code, then its cleanup (`Impl/Residue/Arm.lean`): the stack its
contract reserves zeroed and the registers a callee may change set to
constants (`scrubF`), but for key expansion, whose cleanup zeroes only the
words of that stack that the residue analysis (`Arm.rtaint`) finds may
differ between two runs (`Impl/Residue/ArmSel.lean`, `scrubSel`,
`expandKeyWords`, offsets in words from its lowest address). Key expansion and ECB keep their working space in a
frame of 96 and 256 bytes (`withRegScratchWiped`); the modes keep theirs in
a frame of 64 bytes (`withStackScratchWiped`) and call ECB's code, so their
contracts reserve 320 bytes. None returns a value.
-/

@[expose] public section

namespace VG.Impl.Blowfish.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm VG.Impl.StackScratch.Arm

/-- The words key expansion leaves secret. -/
def expandKeyWords : List Nat := List.range' 20 4

/-- `vg_blowfish_expand_key`. -/
def expandKey : Prog isa := scrubSel 0 96 expandKeyWords (withRegScratchWiped 96 .r3 20 Arm.expandKey)

/-- `vg_blowfish_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrubF 0 256 (Arm.ecbCode true)

/-- `vg_blowfish_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubF 0 256 (Arm.ecbCode false)

/-- `vg_blowfish_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := scrubF 0 320 (withStackScratchWiped 64 0 14 Arm.cbcEncryptChained)

/-- `vg_blowfish_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := scrubF 0 320 (withStackScratchWiped 64 0 14 Arm.cbcDecryptChained)

/-- `vg_blowfish_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := scrubF 0 320 (withStackScratchWiped 64 0 14 Arm.cfbEncrypt)

/-- `vg_blowfish_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := scrubF 0 320 (withStackScratchWiped 64 0 14 Arm.cfbDecrypt)

/-- `vg_blowfish_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubF 0 320 (withStackScratchWiped 64 0 14 Arm.cfbEncryptFinal)

/-- `vg_blowfish_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubF 0 320 (withStackScratchWiped 64 0 14 Arm.cfbDecryptFinal)

/-- `vg_blowfish_ofb`. -/
def ofb : Prog isa := scrubF 0 320 (withStackScratchWiped 64 0 14 Arm.ofb)

/-- `vg_blowfish_ofb_final`. -/
def ofbFinal : Prog isa := scrubF 0 320 (withStackScratchWiped 64 0 14 Arm.ofbFinal)

end VG.Impl.Blowfish.Arm.Fn
