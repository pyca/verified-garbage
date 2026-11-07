module

public import VerifiedGarbage.Impl.Seed.RISCV64.Modes
public import VerifiedGarbage.Impl.Modes.RISCV64.SeqFinal

/-!
# SEED-CFB128 and SEED-OFB of a message's last piece on RISC-V

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = a0, iv = a1, data = a2,
len = a3): the modes' CFB and OFB over a message's last piece, of any length
(`Impl/Modes/RISCV64/SeqFinal.lean`), over Seed's one-block encryption core
(`Modes.lean`), in its frame.
-/

@[expose] public section

namespace VG.Impl.Seed.RISCV64

open VG.RISCV64

/-- `vg_seed_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt 1).seqFinal (Modes.Mode.cfbEnc 4)

/-- `vg_seed_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt 1).seqFinal (Modes.Mode.cfbDec 4)

/-- `vg_seed_ofb_final`. -/
def ofbFinal : Prog isa := (dirCore .encrypt 1).seqFinal (Modes.Mode.ofb 4)

end VG.Impl.Seed.RISCV64
