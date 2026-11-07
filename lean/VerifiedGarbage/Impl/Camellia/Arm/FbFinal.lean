module

public import VerifiedGarbage.Impl.Camellia.Arm.Fb
public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal

/-!
# Camellia-CFB128 of a message's last piece on ARMv7

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = r0, rounds = r1,
iv = r2, data = r3, len = [sp], scratch = [sp + 4]): the generic CFB over a
message's last piece, of any length (`Impl/Modes/Arm/SeqFinal.lean`), over
Camellia's ECB encryption, with the arguments of `cfbEncrypt` but the data's
length in bytes.
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbEnc

/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbDecF

end VG.Impl.Camellia.Arm
