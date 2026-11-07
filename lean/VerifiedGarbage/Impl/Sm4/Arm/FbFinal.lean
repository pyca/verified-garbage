module

public import VerifiedGarbage.Impl.Sm4.Arm.Fb
public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal

/-!
# SM4-CFB128 of a message's last piece on ARMv7

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = r0, iv = r1, data = r2,
len = r3, scratch = [sp]): the generic CFB over a message's last piece, of
any length (`Impl/Modes/Arm/SeqFinal.lean`), over Sm4's ECB function, with
the arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_sm4_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbEnc

/-- `vg_sm4_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbDecF

end VG.Impl.Sm4.Arm
