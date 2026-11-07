module

public import VerifiedGarbage.Impl.Blowfish.Arm.Modes
public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal

/-!
# Blowfish-CFB64 of a message's last piece on ARMv7

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = r0, iv = r1, data = r2,
len = r3, scratch = [sp]): the generic CFB over a message's last piece, of
any length (`Impl/Modes/Arm/SeqFinal.lean`), over Blowfish's ECB function, with
the arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Blowfish.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_blowfish_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (ecbCore true).seqFinal cfbEnc

/-- `vg_blowfish_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (ecbCore true).seqFinal cfbDecF

end VG.Impl.Blowfish.Arm
