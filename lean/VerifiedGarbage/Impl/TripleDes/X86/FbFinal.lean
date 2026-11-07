module

public import VerifiedGarbage.Impl.TripleDes.X86.Fb
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal

/-!
# Triple DES-CFB64 of a message's last piece on x86 (32-bit)

`cfbEncryptFinal` and `cfbDecryptFinal` (cdecl: schedule, iv, data, len,
scratch): the modes' CFB over a message's last piece, of any length
(`Impl/Modes/X86/SeqFinal.lean`), over Triple DES's core in the encryption
direction, with the arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86

open VG.X86

/-- `vg_triple_des_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbEnc 2)

/-- `vg_triple_des_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbDec 2)

end VG.Impl.TripleDes.X86
