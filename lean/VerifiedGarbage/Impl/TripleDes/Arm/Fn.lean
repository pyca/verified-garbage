module

public import VerifiedGarbage.Impl.TripleDes.Arm.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.Arm.Cbc
public import VerifiedGarbage.Impl.TripleDes.Arm.Wide
public import VerifiedGarbage.Impl.TripleDes.Arm.Fb
public import VerifiedGarbage.Impl.TripleDes.Arm.FbFinal
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.ArmSel

/-!
# Triple DES on ARMv7, as emitted

Each function's code, which wipes its own working space, followed by its
cleanup (`Impl/Scrub/ArmSel.lean`, `scrubSel`): of the stack its contract
reserves, where its frames were, only the words that the residue analysis
(`Arm.rtaint`) finds may differ between two runs zeroed (`…Words`, offsets in
words from the lowest address of that stack), and the registers a callee may
change, but its result, set to constants.
`Proof/TripleDes/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.TripleDes.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- The words key expansion and ECB leave secret: none. -/
def noWords : List Nat := []

/-- The words the modes one block at a time leave secret. -/
def modeWords : List Nat := List.range' 256 2

/-- The words the modes in groups of blocks leave secret. -/
def wideWords : List Nat := List.range' 0 2 ++ List.range' 258 2

/-- `vg_triple_des_expand_key`. -/
def expandKey : Prog isa := scrubSel 0 512 noWords (Impl.StackScratch.Arm.withRegScratchWiped 512 .r3 128 Impl.TripleDes.Arm.Key.expandKey)

/-- `vg_triple_des_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrubSel 0 1024 noWords (Impl.TripleDes.Arm.ecbCode .encrypt)

/-- `vg_triple_des_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubSel 0 1024 noWords (Impl.TripleDes.Arm.ecbCode .decrypt)

/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncrypt : Prog isa := scrubSel 0 1088 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cbcEncryptChained)

/-- `vg_triple_des_cbc_decrypt_chained`. -/
def cbcDecrypt : Prog isa := scrubSel 0 1040 wideWords (Impl.StackScratch.Arm.withStackScratchWiped 1040 0 256 Impl.TripleDes.Arm.Wide.cbcDecrypt)

/-- `vg_triple_des_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := scrubSel 0 1088 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncrypt)

/-- `vg_triple_des_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := scrubSel 0 1040 wideWords (Impl.StackScratch.Arm.withStackScratchWiped 1040 0 256 Impl.TripleDes.Arm.Wide.cfbDecrypt)

/-- `vg_triple_des_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := scrubSel 0 1088 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbEncryptFinal)

/-- `vg_triple_des_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := scrubSel 0 1088 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfbDecryptFinal)

/-- `vg_triple_des_cfb8_encrypt`. -/
def cfb8Encrypt : Prog isa := scrubSel 0 1088 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Encrypt)

/-- `vg_triple_des_cfb8_decrypt`. -/
def cfb8Decrypt : Prog isa := scrubSel 0 1088 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.cfb8Decrypt)

/-- `vg_triple_des_ofb`. -/
def ofb : Prog isa := scrubSel 0 1088 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofb)

/-- `vg_triple_des_ofb_final`. -/
def ofbFinal : Prog isa := scrubSel 0 1088 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 Impl.TripleDes.Arm.ofbFinal)

end VG.Impl.TripleDes.Arm.Fn
