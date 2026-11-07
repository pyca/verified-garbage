module

public import VerifiedGarbage.Impl.Idea.Arm.Modes
public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal

/-!
# IDEA-CFB64 and IDEA-OFB of a message's last piece on ARMv7

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = r0, iv = r1, data = r2,
len = r3, scratch = [sp]): the generic CFB and OFB over a message's last piece, of
any length (`Impl/Modes/Arm/SeqFinal.lean`), over IDEA's ECB function, with
the arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Idea.Arm

open VG.Arm VG.Impl.Modes.Arm

/-- `vg_idea_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := ecbCore.seqFinal cfbEnc

/-- `vg_idea_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := ecbCore.seqFinal cfbDecF

/-- `vg_idea_ofb_final`. -/
def ofbFinal : Prog isa := ecbCore.seqFinal VG.Impl.Modes.Arm.ofb

end VG.Impl.Idea.Arm
