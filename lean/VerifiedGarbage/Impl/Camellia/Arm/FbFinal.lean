module

public import VerifiedGarbage.Impl.Camellia.Arm.Fb
public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal

/-!
# Camellia-CFB128 and Camellia-OFB of a message's last piece on ARMv7

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = r0, rounds = r1,
iv = r2, data = r3, len = [sp], scratch = [sp + 4]): the generic CFB and OFB over a
message's last piece, of any length (`Impl/Modes/Arm/SeqFinal.lean`), over
Camellia's ECB encryption, with the arguments of `cfbEncrypt` (and `ofb`) but the data's
length in bytes.
-/

@[expose] public section

namespace VG.Impl.Camellia.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbEnc

/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbDecF

/-- `vg_camellia_ofb_final`. -/
def ofbFinal : Prog isa := (ecbCore .encrypt).seqFinal VG.Impl.Modes.Arm.ofb

end VG.Impl.Camellia.Arm
