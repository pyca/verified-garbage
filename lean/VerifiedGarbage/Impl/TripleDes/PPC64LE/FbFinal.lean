module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Modes
public import VerifiedGarbage.Impl.Modes.PPC64LE.SeqFinal

/-!
# Triple DES-CFB64 and Triple DES-OFB of a message's last piece on PPC64LE

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = r3, iv = r4, data = r5,
len = r6, scratch = r7): the modes' CFB and OFB over a message's last piece, of any
length (`Impl/Modes/PPC64LE/SeqFinal.lean`), over Triple DES's core, with the
arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE

open VG.PPC64LE

/-- `vg_triple_des_cfb64_encrypt_final`, with its scratch buffer as the fifth argument. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbEnc 2)

/-- `vg_triple_des_cfb64_decrypt_final`, with its scratch buffer as the fifth argument. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbDec 2)

/-- `vg_triple_des_ofb_final`, with its scratch buffer as the fifth argument. -/
def ofbFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.ofb 2)

end VG.Impl.TripleDes.PPC64LE
