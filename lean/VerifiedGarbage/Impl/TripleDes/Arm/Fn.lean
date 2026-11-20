module

public import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.Arm.Cbc
public import VerifiedGarbage.Impl.TripleDes.Arm.Wide
public import VerifiedGarbage.Impl.TripleDes.Arm.Fb
public import VerifiedGarbage.Impl.TripleDes.Arm.FbFinal
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# Triple DES on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Residue/Arm.lean`,
`scrubF`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change, but its result, set to constants.
`Proof/TripleDes/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.TripleDes.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_triple_des_expand_key`. -/
def expandKey : Prog isa := scrubF 0 512 (Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.TripleDes.Arm.Key.expandKey)

/-- `vg_triple_des_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrubF 0 1024 (Impl.TripleDes.Arm.ecbCode .encrypt)

/-- `vg_triple_des_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubF 0 1024 (Impl.TripleDes.Arm.ecbCode .decrypt)

/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncrypt : Prog isa := scrubF 0 1088 (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcEncryptChained)

/-- `vg_triple_des_cbc_decrypt_chained`. -/
def cbcDecrypt : Prog isa := scrubF 0 1040 (Impl.StackScratch.Arm.withStackScratchWiped 1040 0 256 Impl.TripleDes.Arm.Wide.cbcDecrypt)

/-- `vg_triple_des_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := scrubF 0 1088 (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncrypt)

/-- `vg_triple_des_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := scrubF 0 1040 (Impl.StackScratch.Arm.withStackScratchWiped 1040 0 256 Impl.TripleDes.Arm.Wide.cfbDecrypt)

/-- `vg_triple_des_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubF 0 1088 (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncryptFinal)

/-- `vg_triple_des_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubF 0 1088 (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbDecryptFinal)

/-- `vg_triple_des_cfb8_encrypt`. -/
def cfb8Encrypt : Prog isa := scrubF 0 1088 (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Encrypt)

/-- `vg_triple_des_cfb8_decrypt`. -/
def cfb8Decrypt : Prog isa := scrubF 0 1088 (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Decrypt)

/-- `vg_triple_des_ofb`. -/
def ofb : Prog isa := scrubF 0 1088 (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofb)

/-- `vg_triple_des_ofb_final`. -/
def ofbFinal : Prog isa := scrubF 0 1088 (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofbFinal)

end VG.Impl.TripleDes.Arm.Fn
