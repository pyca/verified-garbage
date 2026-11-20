module

public import VerifiedGarbage.Impl.Camellia.Arm.ExpandKey
public import VerifiedGarbage.Impl.Camellia.Arm.Cbc
public import VerifiedGarbage.Impl.Camellia.Arm.Fb
public import VerifiedGarbage.Impl.Camellia.Arm.FbFinal
public import VerifiedGarbage.Impl.Camellia.Arm.CtrFinal
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# Camellia on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Residue/Arm.lean`,
`scrubF`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change, but its result, set to constants.
`Proof/Camellia/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_camellia_expand_key`. -/
def expandKey : Prog isa := scrubF 0 2720 (Impl.StackScratch.Arm.withRegScratchWiped 2720 .r3 680 Impl.Camellia.Arm.expandKey)

/-- `vg_camellia_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrubF 0 2816 (Impl.Camellia.Arm.ecbCode .encrypt)

/-- `vg_camellia_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubF 0 2816 (Impl.Camellia.Arm.ecbCode .decrypt)

/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncrypt : Prog isa := scrubF 0 2832 (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.cbcEncryptChained)

/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecrypt : Prog isa := scrubF 0 3040 (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cbcDecryptChained)

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := scrubF 0 2832 (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.cfbEncrypt)

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := scrubF 0 3040 (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecrypt)

/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubF 0 2912 (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbEncryptFinal)

/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubF 0 2912 (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.cfbDecryptFinal)

/-- `vg_camellia_ctr`. -/
def ctr : Prog isa := scrubF 0 3040 Impl.Camellia.Arm.ctrFramed

/-- `vg_camellia_ctr_final`. -/
def ctrFinal : Prog isa := scrubF 0 3120 (Impl.StackScratch.Arm.withStackScratchWiped 72 1 14 Impl.Camellia.Arm.ctrFinal)

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa := scrubF 0 2832 (Impl.StackScratch.Arm.withStackScratchWiped 2816 1 698 Impl.Camellia.Arm.ofb)

/-- `vg_camellia_ofb_final`. -/
def ofbFinal : Prog isa := scrubF 0 2912 (Impl.StackScratch.Arm.withStackScratchWiped 88 1 18 Impl.Camellia.Arm.ofbFinal)

end VG.Impl.Camellia.Arm.Fn
