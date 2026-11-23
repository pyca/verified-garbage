module

public import VerifiedGarbage.Impl.Scrub.Arm
public import VerifiedGarbage.Impl.Sm4.Arm.ExpandKey
public import VerifiedGarbage.Impl.Sm4.Arm.SerialCbc
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCbc
public import VerifiedGarbage.Impl.Sm4.Arm.SerialCfb
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCfb
public import VerifiedGarbage.Impl.Sm4.Arm.SerialOfb
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Impl.Sm4.Arm.CtrFinal
public import VerifiedGarbage.Impl.Sm4.Arm.FbFinal

/-!
# SM4's key expansion, ECB and modes on ARMv7, as emitted

Each function is its code with its working space in a frame on the stack
(`withStackScratch`, `withRegScratch`), left as it is, then its cleanup
(`scrubAll`, `Impl/Scrub/Arm.lean`): the stack its contract reserves, where
its frames and those of the code it calls were, zeroed in a loop, and the
registers a callee may change set to constants. That stack is a frame size
of the model, a multiple of 8 that an ARM immediate encodes: ECB's 1480
bytes and the final CFB and OFB functions' 1560 are not, so their cleanup
zeroes 1488 and 1568. `Proof/Sm4/Arm/Scrub.lean` states that each returns
without secret residue.

The modes over a message's last piece call ECB's and CTR's code as it is
verified, without the cleanup, under names of their own
(`vg_sm4_ecb_encrypt_core`, `Impl.Sm4.Arm.ecbCore`; `vg_sm4_ctr_core`,
`Impl.Sm4.Arm.ctrCall`).
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm VG.Impl.StackScratch.Arm

/-- `vg_sm4_expand_key`. -/
def expandKey : Prog isa := scrubAll 0 1456 (withRegScratch 1456 .r2 Impl.Sm4.Arm.expandKey)

/-- `vg_sm4_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrubAll 0 1488 (ecbCall .encrypt)

/-- `vg_sm4_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubAll 0 1488 (ecbCall .decrypt)

/-- `vg_sm4_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := scrubAll 0 1520 (withStackScratch 1520 0 SerialCbc.encrypt)

/-- `vg_sm4_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := scrubAll 0 1520 (withStackScratch 1520 0 BatchCbc.decrypt)

/-- `vg_sm4_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := scrubAll 0 1520 (withStackScratch 1520 0 SerialCfb.encrypt)

/-- `vg_sm4_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := scrubAll 0 1520 (withStackScratch 1520 0 BatchCfb.decrypt)

/-- `vg_sm4_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubAll 0 1568 (withStackScratch 80 0 Impl.Sm4.Arm.cfbEncryptFinal)

/-- `vg_sm4_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubAll 0 1568 (withStackScratch 80 0 Impl.Sm4.Arm.cfbDecryptFinal)

/-- `vg_sm4_ctr`. -/
def ctr : Prog isa := scrubAll 0 1520 (withStackScratch 1520 0 BatchCtr.ctr)

/-- `vg_sm4_ctr_final`. -/
def ctrFinal : Prog isa := scrubAll 0 1584 (withStackScratch 64 0 Impl.Sm4.Arm.ctrFinal)

/-- `vg_sm4_ofb`. -/
def ofb : Prog isa := scrubAll 0 1520 (withStackScratch 1520 0 SerialOfb.crypt)

/-- `vg_sm4_ofb_final`. -/
def ofbFinal : Prog isa := scrubAll 0 1568 (withStackScratch 80 0 Impl.Sm4.Arm.ofbFinal)

end VG.Impl.Sm4.Arm.Fn
