module

public import VerifiedGarbage.Impl.Camellia.RISCV64.Modes
public import VerifiedGarbage.Impl.Modes.RISCV64.SeqFinal

/-!
# Camellia-CFB128 and Camellia-OFB of a message's last piece on RISC-V

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = a0, rounds = a1,
iv = a2, data = a3, len = a4): `modeFn` of the modes' CFB and OFB over a message's
last piece, of any length (`Impl/Modes/RISCV64/SeqFinal.lean`), over
Camellia's encryption core with the rounds `rounds` says (`Modes.lean`), in
its frame.
-/

@[expose] public section

namespace VG.Impl.Camellia.RISCV64

open VG.RISCV64

/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := modeFn fun R => (dirCore .encrypt R).seqFinal (Modes.Mode.cfbEnc 4)

/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := modeFn fun R => (dirCore .encrypt R).seqFinal (Modes.Mode.cfbDec 4)

/-- `vg_camellia_ofb_final`. -/
def ofbFinal : Prog isa := modeFn fun R => (dirCore .encrypt R).seqFinal (Modes.Mode.ofb 4)

end VG.Impl.Camellia.RISCV64
