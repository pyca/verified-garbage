module

public import VerifiedGarbage.Impl.Camellia.PPC64LE.Modes
public import VerifiedGarbage.Impl.Modes.PPC64LE.SeqFinal

/-!
# Camellia-CFB128 and Camellia-OFB of a message's last piece on PPC64LE

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = r3, rounds =
r4, iv = r5, data = r6, len = r7, scratch = r8): the modes' CFB and OFB over a message's last
piece, of any length (`Impl/Modes/PPC64LE/SeqFinal.lean`), over Camellia's
core, wrapped for the two key arguments (`wrap`) as `cfbEncrypt` is, with its
arguments but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Camellia.PPC64LE

open VG.PPC64LE

/-- `vg_camellia_cfb128_encrypt_final`, with its scratch buffer as the sixth argument. -/
def cfbEncryptFinal : Prog isa := wrap ((dirCore .encrypt).seqFinal (Modes.Mode.cfbEnc 4))

/-- `vg_camellia_cfb128_decrypt_final`, with its scratch buffer as the sixth argument. -/
def cfbDecryptFinal : Prog isa := wrap ((dirCore .encrypt).seqFinal (Modes.Mode.cfbDec 4))

/-- `vg_camellia_ofb_final`, with its scratch buffer as the sixth argument. -/
def ofbFinal : Prog isa := wrap ((dirCore .encrypt).seqFinal (Modes.Mode.ofb 4))

end VG.Impl.Camellia.PPC64LE
