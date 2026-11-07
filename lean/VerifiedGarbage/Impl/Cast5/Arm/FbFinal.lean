module

public import VerifiedGarbage.Impl.Cast5.Arm.Modes
public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal

/-!
# CAST5-CFB64 and CAST5-OFB of a message's last piece on ARMv7

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = r0, rounds = r1,
iv = r2, data = r3, len = [sp], scratch = [sp + 4]): the generic CFB and OFB over a
message's last piece, of any length (`Impl/Modes/Arm/SeqFinal.lean`), over
CAST5's ECB encryption, with the arguments of `cfbEncrypt` (and `ofb`) but the data's
length in bytes.
-/

@[expose] public section

namespace VG.Impl.Cast5.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_cast5_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (ecbCore true).seqFinal cfbEnc

/-- `vg_cast5_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (ecbCore true).seqFinal cfbDecF

/-- `vg_cast5_ofb_final`. -/
def ofbFinal : Prog isa := (ecbCore true).seqFinal VG.Impl.Modes.Arm.ofb

end VG.Impl.Cast5.Arm
