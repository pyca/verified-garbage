module

public import VerifiedGarbage.Impl.Seed.Arm.ExpandKey
public import VerifiedGarbage.Impl.Seed.Arm.Modes
public import VerifiedGarbage.Impl.Seed.Arm.FbFinal
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.ArmSel

/-!
# SEED on ARMv7, as emitted

Each function's code, which wipes its own working space, followed by its
cleanup (`Impl/Residue/ArmSel.lean`, `scrubSel`): of the stack its contract
reserves, where its frames were, only the words that the residue analysis
(`Arm.rtaint`) finds may differ between two runs zeroed (`…Words`, offsets in
words from the lowest address of that stack), and the registers a callee may
change set to constants. None returns a value. `Proof/Seed/Arm/Scrub.lean` states that each returns without secret
residue.
-/

@[expose] public section

namespace VG.Impl.Seed.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- The words key expansion and ECB leave secret: none. -/
def noWords : List Nat := []

/-- The words the modes over 832 bytes leave secret. -/
def modeWords : List Nat := List.range' 188 2

/-- The words the modes in groups of blocks, over 960 bytes, leave secret. -/
def wideWords : List Nat := List.range' 220 2

/-- `vg_seed_expand_key`. -/
def expandKey : Prog isa :=
  scrubSel 0 752 noWords (Impl.StackScratch.Arm.withRegScratchWiped 752 .r2 188 Impl.Seed.Arm.expandKey)

/-- `vg_seed_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrubSel 0 752 noWords (Impl.Seed.Arm.ecbCode .encrypt)

/-- `vg_seed_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubSel 0 752 noWords (Impl.Seed.Arm.ecbCode .decrypt)

/-- `vg_seed_cbc_encrypt_chained`. -/
def cbcEncrypt : Prog isa :=
  scrubSel 0 832 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcEncryptChained)

/-- `vg_seed_cbc_decrypt_chained`. -/
def cbcDecrypt : Prog isa :=
  scrubSel 0 960 wideWords (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcDecryptChained)

/-- `vg_seed_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa :=
  scrubSel 0 832 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbEncrypt)

/-- `vg_seed_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa :=
  scrubSel 0 960 wideWords (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbDecrypt)

/-- `vg_seed_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa :=
  scrubSel 0 832 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbEncryptFinal)

/-- `vg_seed_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa :=
  scrubSel 0 832 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbDecryptFinal)

/-- `vg_seed_ofb`. -/
def ofb : Prog isa :=
  scrubSel 0 832 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.ofb)

/-- `vg_seed_ofb_final`. -/
def ofbFinal : Prog isa :=
  scrubSel 0 832 modeWords (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.ofbFinal)

end VG.Impl.Seed.Arm.Fn
