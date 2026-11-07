module

public import VerifiedGarbage.Impl.Sm4.X86.Fb
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal

/-!
# SM4-CFB128 of a message's last piece on x86 (32-bit)

`cfbEncryptFinal` and `cfbDecryptFinal` (cdecl: schedule, iv, data, len,
scratch): the modes' CFB over a message's last piece, of any length
(`Impl/Modes/X86/SeqFinal.lean`), over SM4's core in the encryption
direction, with the arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86

open VG.X86

/-- `vg_sm4_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbEnc 4)

/-- `vg_sm4_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbDec 4)

end VG.Impl.Sm4.X86
