module

public import VerifiedGarbage.Impl.Blowfish.X86.Modes
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal

/-!
# Blowfish-CFB64 of a message's last piece on x86 (32-bit)

`cfbEncryptFinal` and `cfbDecryptFinal` (cdecl: schedule, iv, data, len,
scratch): the modes' CFB over a message's last piece, of any length
(`Impl/Modes/X86/SeqFinal.lean`), over Blowfish's encrypting core, with the
arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Blowfish.X86

open VG.X86

/-- `vg_blowfish_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore true).seqFinal (Modes.Mode.cfbEnc 2)

/-- `vg_blowfish_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore true).seqFinal (Modes.Mode.cfbDec 2)

end VG.Impl.Blowfish.X86
