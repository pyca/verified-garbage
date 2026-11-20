module

public import VerifiedGarbage.Impl.Seed.Arm.ExpandKey
public import VerifiedGarbage.Impl.Seed.Arm.Modes
public import VerifiedGarbage.Impl.Seed.Arm.FbFinal
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# SEED on ARMv7, as emitted

Each function's code followed by its cleanup (`Impl/Residue/Arm.lean`,
`scrubF`): the stack its contract reserves, where its frames were, zeroed,
and the registers a callee may change set to constants. None returns a
value. `Proof/Seed/Arm/Scrub.lean` states that each returns without secret
residue.
-/

@[expose] public section

namespace VG.Impl.Seed.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_seed_expand_key`. -/
def expandKey : Prog isa :=
  scrubF 0 752 (Impl.StackScratch.Arm.withRegScratchWiped 752 .r2 188 Impl.Seed.Arm.expandKey)

/-- `vg_seed_ecb_encrypt`. -/
def ecbEncrypt : Prog isa := scrubF 0 752 (Impl.Seed.Arm.ecbCode .encrypt)

/-- `vg_seed_ecb_decrypt`. -/
def ecbDecrypt : Prog isa := scrubF 0 752 (Impl.Seed.Arm.ecbCode .decrypt)

/-- `vg_seed_cbc_encrypt_chained`. -/
def cbcEncrypt : Prog isa :=
  scrubF 0 832 (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcEncryptChained)

/-- `vg_seed_cbc_decrypt_chained`. -/
def cbcDecrypt : Prog isa :=
  scrubF 0 960 (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cbcDecryptChained)

/-- `vg_seed_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa :=
  scrubF 0 832 (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbEncrypt)

/-- `vg_seed_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa :=
  scrubF 0 960 (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbDecrypt)

/-- `vg_seed_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa :=
  scrubF 0 832 (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbEncryptFinal)

/-- `vg_seed_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa :=
  scrubF 0 832 (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.cfbDecryptFinal)

/-- `vg_seed_ofb`. -/
def ofb : Prog isa :=
  scrubF 0 832 (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.ofb)

/-- `vg_seed_ofb_final`. -/
def ofbFinal : Prog isa :=
  scrubF 0 832 (Impl.StackScratch.Arm.withStackScratchWiped 80 0 18 Impl.Seed.Arm.ofbFinal)

end VG.Impl.Seed.Arm.Fn
