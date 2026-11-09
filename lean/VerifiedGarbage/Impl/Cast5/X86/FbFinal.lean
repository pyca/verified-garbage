module

public import VerifiedGarbage.Impl.Cast5.X86.Modes
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal

/-!
# CAST5-CFB64 and CAST5-OFB of a message's last piece on x86 (32-bit)

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (cdecl: schedule, rounds, iv, data,
len, scratch): the modes' CFB and OFB over a message's last piece, of any length
(`Impl/Modes/X86/SeqFinal.lean`), over CAST5's encrypting core, with the
arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Cast5.X86.Modes

open VG.X86

/-- `vg_cast5_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore true).seqFinal (Impl.Modes.Mode.cfbEnc 2)

/-- `vg_cast5_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore true).seqFinal (Impl.Modes.Mode.cfbDec 2)

/-- `vg_cast5_ofb_final`. -/
def ofbFinal : Prog isa := (dirCore true).seqFinal (Impl.Modes.Mode.ofb 2)

end VG.Impl.Cast5.X86.Modes
