module

public import VerifiedGarbage.Impl.Scrub.ArmSel
public import VerifiedGarbage.Impl.Sm4.Arm.ExpandKey
public import VerifiedGarbage.Impl.Sm4.Arm.SerialCbc
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCbc
public import VerifiedGarbage.Impl.Sm4.Arm.SerialCfb
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCfb
public import VerifiedGarbage.Impl.Sm4.Arm.SerialOfb
public import VerifiedGarbage.Impl.Sm4.Arm.CtrFinal
public import VerifiedGarbage.Impl.Sm4.Arm.FbFinal

/-!
# SM4's key expansion, ECB and modes on ARMv7, as emitted

Each function is its code with its working space in a frame on the stack
(`withStackScratchWiped`, `withRegScratchWiped`), which it wipes, then its
cleanup (`Impl/Scrub/ArmSel.lean`, `scrubSel`): of the stack its contract
reserves, where its frames were, only the words that the residue analysis
(`Arm.rtaint`) finds may differ between two runs zeroed (`…Words`, offsets in
words from the lowest address of that stack), and the registers a callee may
change set to constants. What is left is the stack arguments and buffer
addresses the code copies into its frames and its innermost frames. That
stack is a frame size of the model, a multiple of 8 that an ARM immediate
encodes: ECB's 1480 bytes and the final CFB and OFB functions' 1560 are not,
so their cleanup is within 1488 and 1568. `Proof/Sm4/Arm/Scrub.lean` states
that each returns without secret residue.

The modes over a message's last piece call ECB's and CTR's code as it is
verified, without the cleanup, under names of their own
(`vg_sm4_ecb_encrypt_core`, `Impl.Sm4.Arm.ecbCore`; `vg_sm4_ctr_core`,
`Impl.Sm4.Arm.ctrCall`).
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm VG.Impl.StackScratch.Arm

/-- The words the key expansion leaves secret: none. -/
def expandKeyWords : List Nat := []

/-- The words ECB leaves secret. -/
def ecbWords : List Nat := List.range' 2 2 ++ List.range' 368 4

/-- The words the modes over whole blocks leave secret. -/
def modeWords : List Nat := List.range' 0 2

/-- The words CFB and OFB over a message's last piece leave secret. -/
def finalWords : List Nat := List.range' 2 2 ++ List.range' 368 6

/-- The words CTR over a message's last piece leaves secret. -/
def ctrFinalWords : List Nat := List.range' 0 2 ++ List.range' 380 2

/-- `vg_sm4_expand_key`. -/
def expandKey : Prog isa := scrubSel 0 1456 expandKeyWords (withRegScratchWiped 1456 .r2 364 Impl.Sm4.Arm.expandKey)

/-- `vg_sm4_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrubSel 0 1488 ecbWords (ecbCall .encrypt)

/-- `vg_sm4_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubSel 0 1488 ecbWords (ecbCall .decrypt)

/-- `vg_sm4_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := scrubSel 0 1520 modeWords (withStackScratchWiped 1520 0 378 SerialCbc.encrypt)

/-- `vg_sm4_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := scrubSel 0 1520 modeWords (withStackScratchWiped 1520 0 378 BatchCbc.decrypt)

/-- `vg_sm4_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := scrubSel 0 1520 modeWords (withStackScratchWiped 1520 0 378 SerialCfb.encrypt)

/-- `vg_sm4_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := scrubSel 0 1520 modeWords (withStackScratchWiped 1520 0 378 BatchCfb.decrypt)

/-- `vg_sm4_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubSel 0 1568 finalWords (withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbEncryptFinal)

/-- `vg_sm4_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubSel 0 1568 finalWords (withStackScratchWiped 80 0 18 Impl.Sm4.Arm.cfbDecryptFinal)

/-- `vg_sm4_ctr`. -/
def ctr : Prog isa := scrubSel 0 1520 modeWords ctrFramed

/-- `vg_sm4_ctr_final`. -/
def ctrFinal : Prog isa := scrubSel 0 1584 ctrFinalWords (withStackScratchWiped 64 0 14 Impl.Sm4.Arm.ctrFinal)

/-- `vg_sm4_ofb`. -/
def ofb : Prog isa := scrubSel 0 1520 modeWords (withStackScratchWiped 1520 0 378 SerialOfb.crypt)

/-- `vg_sm4_ofb_final`. -/
def ofbFinal : Prog isa := scrubSel 0 1568 finalWords (withStackScratchWiped 80 0 18 Impl.Sm4.Arm.ofbFinal)

end VG.Impl.Sm4.Arm.Fn
