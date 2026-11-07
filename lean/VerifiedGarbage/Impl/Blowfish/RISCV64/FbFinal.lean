module

public import VerifiedGarbage.Impl.Blowfish.RISCV64.Modes
public import VerifiedGarbage.Impl.Modes.RISCV64.SeqFinal

/-!
# Blowfish-CFB64 of a message's last piece on RISC-V

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = a0, iv = a1, data = a2,
len = a3): the modes' CFB over a message's last piece, of any length
(`Impl/Modes/RISCV64/SeqFinal.lean`), over Blowfish's one-block encryption core
(`Modes.lean`), in its frame.
-/

@[expose] public section

namespace VG.Impl.Blowfish.RISCV64

open VG.RISCV64

/-- `vg_blowfish_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore true).seqFinal (Modes.Mode.cfbEnc 2)

/-- `vg_blowfish_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore true).seqFinal (Modes.Mode.cfbDec 2)

end VG.Impl.Blowfish.RISCV64
