module

public import VerifiedGarbage.Impl.Camellia.RISCV64.Modes
public import VerifiedGarbage.Impl.Modes.RISCV64.SeqFinal

/-!
# Camellia-CFB128 of a message's last piece on RISC-V

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = a0, rounds = a1,
iv = a2, data = a3, len = a4): `modeFn` of the modes' CFB over a message's
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

end VG.Impl.Camellia.RISCV64
