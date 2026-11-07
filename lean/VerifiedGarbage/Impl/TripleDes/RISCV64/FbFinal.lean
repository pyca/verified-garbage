module

public import VerifiedGarbage.Impl.TripleDes.RISCV64.Modes
public import VerifiedGarbage.Impl.Modes.RISCV64.SeqFinal

/-!
# Triple DES-CFB64 and Triple DES-OFB of a message's last piece on RISC-V

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = a0, iv = a1, data = a2,
len = a3): the modes' CFB and OFB over a message's last piece, of any length
(`Impl/Modes/RISCV64/SeqFinal.lean`), over TripleDes's one-block encryption core
(`Modes.lean`), in its frame.
-/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64

open VG.RISCV64

/-- `vg_triple_des_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbEnc 2)

/-- `vg_triple_des_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.cfbDec 2)

/-- `vg_triple_des_ofb_final`. -/
def ofbFinal : Prog isa := (dirCore .encrypt).seqFinal (Modes.Mode.ofb 2)

end VG.Impl.TripleDes.RISCV64
