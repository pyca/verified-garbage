module

public import VerifiedGarbage.Impl.Seed.Arm.ExpandKey
public import VerifiedGarbage.Impl.Seed.Arm.Modes
public import VerifiedGarbage.Impl.Seed.Arm.FbFinal
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# SEED on ARMv7, as emitted

Each function's code, with its working space in a frame on the stack left as
it is (`withStackScratch`, `withRegScratch`), and the ECB core it calls
(`Modes.lean`, `ecbCore`) its own, followed by its cleanup (`scrubAll`,
`Impl/Scrub/Arm.lean`): the stack its contract reserves, where its frames and
those of the code it calls were, zeroed in a loop, and the registers a
callee may change set to constants. None returns a value.
`Proof/Seed/Arm/Scrub.lean` states that each returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Seed.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_seed_expand_key`. -/
def expandKey : Prog isa :=
  scrubAll 0 752 (Impl.StackScratch.Arm.withRegScratch 752 .r2 Impl.Seed.Arm.expandKey)

-- `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt` (`ecbEncrypt`, `ecbDecrypt`,
-- calls of the ECB cores) are in `Modes.lean`, as the modes call them.

/-- `vg_seed_cbc_encrypt_chained`. -/
def cbcEncrypt : Prog isa :=
  scrubAll 0 832 (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cbcEncryptChained)

/-- `vg_seed_cbc_decrypt_chained`. -/
def cbcDecrypt : Prog isa :=
  scrubAll 0 960 (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cbcDecryptChained)

/-- `vg_seed_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa :=
  scrubAll 0 832 (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbEncrypt)

/-- `vg_seed_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa :=
  scrubAll 0 960 (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbDecrypt)

/-- `vg_seed_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa :=
  scrubAll 0 832 (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbEncryptFinal)

/-- `vg_seed_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa :=
  scrubAll 0 832 (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.cfbDecryptFinal)

/-- `vg_seed_ofb`. -/
def ofb : Prog isa :=
  scrubAll 0 832 (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.ofb)

/-- `vg_seed_ofb_final`. -/
def ofbFinal : Prog isa :=
  scrubAll 0 832 (Impl.StackScratch.Arm.withStackScratch 80 0 Impl.Seed.Arm.ofbFinal)

end VG.Impl.Seed.Arm.Fn
