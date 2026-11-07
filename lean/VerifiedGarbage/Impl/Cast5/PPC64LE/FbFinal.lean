module

public import VerifiedGarbage.Impl.Cast5.PPC64LE.Modes
public import VerifiedGarbage.Impl.Modes.PPC64LE.SeqFinal

/-!
# CAST5-CFB64 of a message's last piece on PPC64LE

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = r3, rounds = r4, iv =
r5, data = r6, len = r7, scratch = r8): the modes' CFB over a message's last
piece, of any length (`Impl/Modes/PPC64LE/SeqFinal.lean`), over CAST5's core
with the count of rounds `rounds` says (`modeFn`), as `cfbEncrypt` is, with
its arguments but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Cast5.PPC64LE

open VG.PPC64LE

/-- `vg_cast5_cfb64_encrypt_final`, with its scratch buffer as the sixth argument. -/
def cfbEncryptFinal : Prog isa := modeFn fun n => (dirCore true n).seqFinal (Modes.Mode.cfbEnc 2)

/-- `vg_cast5_cfb64_decrypt_final`, with its scratch buffer as the sixth argument. -/
def cfbDecryptFinal : Prog isa := modeFn fun n => (dirCore true n).seqFinal (Modes.Mode.cfbDec 2)

end VG.Impl.Cast5.PPC64LE
