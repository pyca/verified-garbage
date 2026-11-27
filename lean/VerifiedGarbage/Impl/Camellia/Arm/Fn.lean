module

public import VerifiedGarbage.Impl.Camellia.Arm.ExpandKey
public import VerifiedGarbage.Impl.Camellia.Arm.Cbc
public import VerifiedGarbage.Impl.Camellia.Arm.Fb
public import VerifiedGarbage.Impl.Camellia.Arm.FbFinal
public import VerifiedGarbage.Impl.Camellia.Arm.CtrFinal
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# Camellia on ARMv7, as emitted

Each function's code, with its working space in a frame on the stack left as
it is (`withStackScratch`, `withRegScratch`), and the ECB core it calls
(`Cbc.lean`, `ecbCore`) its own, followed by its cleanup (`scrubAll`,
`Impl/Scrub/Arm.lean`): the stack its contract reserves, where its frames and
those of the code it calls were, zeroed in a loop, and the registers a
callee may change, but its result, set to constants.
`Proof/Camellia/Arm/Scrub.lean` states that each returns without secret
residue.
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_camellia_expand_key`. -/
def expandKey : Prog isa := scrubAll 0 2720 (Impl.StackScratch.Arm.withRegScratch 2720 .r3 Impl.Camellia.Arm.expandKey)

-- `vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt` (`ecbEncrypt`,
-- `ecbDecrypt`, calls of the ECB cores) are in `Cbc.lean`, with the cores.

/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncrypt : Prog isa := scrubAll 0 2832 (Impl.StackScratch.Arm.withStackScratch 2816 1 Impl.Camellia.Arm.cbcEncryptChained)

/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecrypt : Prog isa := scrubAll 0 3040 (Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cbcDecryptChained)

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := scrubAll 0 2832 (Impl.StackScratch.Arm.withStackScratch 2816 1 Impl.Camellia.Arm.cfbEncrypt)

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := scrubAll 0 3040 (Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cfbDecrypt)

/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubAll 0 2912 (Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cfbEncryptFinal)

/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubAll 0 2912 (Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.cfbDecryptFinal)

/-- `vg_camellia_ctr`. -/
def ctr : Prog isa := scrubAll 0 3040 Impl.Camellia.Arm.ctrFramed

/-- `vg_camellia_ctr_final`. -/
def ctrFinal : Prog isa := scrubAll 0 3120 (Impl.StackScratch.Arm.withStackScratch 72 1 Impl.Camellia.Arm.ctrFinal)

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa := scrubAll 0 2832 (Impl.StackScratch.Arm.withStackScratch 2816 1 Impl.Camellia.Arm.ofb)

/-- `vg_camellia_ofb_final`. -/
def ofbFinal : Prog isa := scrubAll 0 2912 (Impl.StackScratch.Arm.withStackScratch 88 1 Impl.Camellia.Arm.ofbFinal)

end VG.Impl.Camellia.Arm.Fn
