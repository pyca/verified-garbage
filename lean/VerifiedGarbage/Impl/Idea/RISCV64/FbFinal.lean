module

public import VerifiedGarbage.Impl.Idea.RISCV64.Modes
public import VerifiedGarbage.Impl.Modes.RISCV64.SeqFinal

/-!
# IDEA-CFB64 of a message's last piece on RISC-V

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = a0, iv = a1, data = a2,
len = a3): the modes' CFB over a message's last piece, of any length
(`Impl/Modes/RISCV64/SeqFinal.lean`), over IDEA's core (`Modes.lean`), in
the whole-block functions' frame.
-/

@[expose] public section

namespace VG.Impl.Idea.RISCV64

open VG.RISCV64

/-- `vg_idea_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := core.seqFinal (Modes.Mode.cfbEnc 2)

/-- `vg_idea_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := core.seqFinal (Modes.Mode.cfbDec 2)

end VG.Impl.Idea.RISCV64
