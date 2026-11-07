module

public import VerifiedGarbage.Impl.Camellia.X86.Modes
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal

/-!
# Camellia-CFB128 of a message's last piece on x86 (32-bit)

`cfbEncryptFinal` and `cfbDecryptFinal` (cdecl: schedule, rounds, iv, data, len,
scratch): the modes' CFB over a message's last piece, of any length
(`Impl/Modes/X86/SeqFinal.lean`), over Camellia's core in the encryption
direction, with the arguments of `cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86

open VG.X86

/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbEnc 4)

/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbDec 4)

end VG.Impl.Camellia.X86
