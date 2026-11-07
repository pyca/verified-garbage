module

public import VerifiedGarbage.Impl.Blowfish.PPC64LE.Modes
public import VerifiedGarbage.Impl.Modes.PPC64LE.SeqFinal

/-!
# Blowfish-CFB64 and Blowfish-OFB of a message's last piece on PPC64LE

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = r3, iv = r4,
data = r5, len = r6, scratch = r7): the modes' CFB and OFB over a message's last piece, of any
length (`Impl/Modes/PPC64LE/SeqFinal.lean`), over Blowfish's core, with the
arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Blowfish.PPC64LE

open VG.PPC64LE

/-- `vg_blowfish_cfb64_encrypt_final`, with its scratch buffer as the fifth argument. -/
def cfbEncryptFinal : Prog isa := (dirCore true).seqFinal (Modes.Mode.cfbEnc 2)

/-- `vg_blowfish_cfb64_decrypt_final`, with its scratch buffer as the fifth argument. -/
def cfbDecryptFinal : Prog isa := (dirCore true).seqFinal (Modes.Mode.cfbDec 2)

/-- `vg_blowfish_ofb_final`, with its scratch buffer as the fifth argument. -/
def ofbFinal : Prog isa := (dirCore true).seqFinal (Modes.Mode.ofb 2)

end VG.Impl.Blowfish.PPC64LE
