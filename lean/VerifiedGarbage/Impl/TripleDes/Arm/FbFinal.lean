module

public import VerifiedGarbage.Impl.TripleDes.Arm.Fb
public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal

/-!
# Triple DES-CFB64 and Triple DES-OFB of a message's last piece on ARMv7

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = r0, iv = r1, data = r2,
len = r3, scratch = [sp]): the generic CFB and OFB over a message's last piece, of
any length (`Impl/Modes/Arm/SeqFinal.lean`), over Triple DES's ECB function, with
the arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.TripleDes.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_triple_des_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbEnc

/-- `vg_triple_des_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (ecbCore .encrypt).seqFinal cfbDecF

/-- `vg_tripledes_ofb_final`. -/
def ofbFinal : Prog isa := (ecbCore .encrypt).seqFinal VG.Impl.Modes.Arm.ofb

end VG.Impl.TripleDes.Arm
