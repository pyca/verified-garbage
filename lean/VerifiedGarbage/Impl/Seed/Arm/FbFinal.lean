module

public import VerifiedGarbage.Impl.Seed.Arm.Modes
public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal

/-!
# SEED-CFB128 of a message's last piece on ARMv7

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = r0, iv = r1, data = r2,
len = r3, scratch = [sp]): the generic CFB over a message's last piece, of
any length (`Impl/Modes/Arm/SeqFinal.lean`), over SEED's ECB function, with
the arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Seed.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_seed_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbEnc

/-- `vg_seed_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbDecF

end VG.Impl.Seed.Arm
