module

public import VerifiedGarbage.Impl.Sm4.RISCV64.Modes
public import VerifiedGarbage.Impl.Modes.RISCV64.SeqFinal

/-!
# SM4-CFB128 of a message's last piece on RISC-V

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = a0, iv = a1, data = a2,
len = a3): the modes' CFB over a message's last piece, of any length
(`Impl/Modes/RISCV64/SeqFinal.lean`), over Sm4's one-block encryption core
(`Modes.lean`), in its frame.
-/

@[expose] public section

namespace VG.Impl.Sm4.RISCV64

open VG.RISCV64

/-- `vg_sm4_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbEnc 4)

/-- `vg_sm4_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbDec 4)

end VG.Impl.Sm4.RISCV64
