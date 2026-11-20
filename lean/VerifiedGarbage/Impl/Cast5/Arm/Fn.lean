module

public import VerifiedGarbage.Impl.Cast5.Arm.FbFinal
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# CAST5's functions on ARMv7, as emitted

Each is its code, then its cleanup (`Impl/Residue/Arm.lean`): the registers
a callee may change set to constants. Key expansion and ECB keep their
working space in their caller's `scratch` and have no frames (`scrub`); the
modes keep theirs, with ECB's, in a frame of 328 bytes
(`withStackScratchWiped`) and call ECB's code in a frame of 8 more, so the
336 bytes their contracts reserve are zeroed first (`scrubF`). None returns
a value.
-/

@[expose] public section

namespace VG.Impl.Cast5.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm VG.Impl.StackScratch.Arm

/-- `vg_cast5_expand_key`. -/
def expandKey : Prog isa := scrub 0 Arm.expandKey

/-- `vg_cast5_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrub 0 Arm.ecbEncrypt

/-- `vg_cast5_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrub 0 Arm.ecbDecrypt

/-- `vg_cast5_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := scrubF 0 336 (withStackScratchWiped 328 1 78 Arm.cbcEncryptChained)

/-- `vg_cast5_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := scrubF 0 336 (withStackScratchWiped 328 1 78 Arm.cbcDecryptChained)

/-- `vg_cast5_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := scrubF 0 336 (withStackScratchWiped 328 1 78 Arm.cfbEncrypt)

/-- `vg_cast5_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := scrubF 0 336 (withStackScratchWiped 328 1 78 Arm.cfbDecrypt)

/-- `vg_cast5_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubF 0 336 (withStackScratchWiped 328 1 78 Arm.cfbEncryptFinal)

/-- `vg_cast5_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubF 0 336 (withStackScratchWiped 328 1 78 Arm.cfbDecryptFinal)

/-- `vg_cast5_ofb`. -/
def ofb : Prog isa := scrubF 0 336 (withStackScratchWiped 328 1 78 Arm.ofb)

/-- `vg_cast5_ofb_final`. -/
def ofbFinal : Prog isa := scrubF 0 336 (withStackScratchWiped 328 1 78 Arm.ofbFinal)

end VG.Impl.Cast5.Arm.Fn
