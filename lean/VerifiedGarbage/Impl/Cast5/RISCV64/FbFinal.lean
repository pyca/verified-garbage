module

public import VerifiedGarbage.Impl.Cast5.RISCV64.Modes
public import VerifiedGarbage.Impl.Modes.RISCV64.SeqFinal

/-!
# CAST5-CFB64 and CAST5-OFB of a message's last piece on RISC-V

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = a0, rounds = a1,
iv = a2, data = a3, len = a4): `modeFn` of the modes' CFB and OFB over a message's
last piece, of any length (`Impl/Modes/RISCV64/SeqFinal.lean`), over
CAST5's encryption core with the rounds `rounds` says (`Modes.lean`), in
its frame.
-/

@[expose] public section

namespace VG.Impl.Cast5.RISCV64

open VG.RISCV64

/-- `vg_cast5_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := modeFn fun n => (dirCore true n).seqFinal (Modes.Mode.cfbEnc 2)

/-- `vg_cast5_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := modeFn fun n => (dirCore true n).seqFinal (Modes.Mode.cfbDec 2)

/-- `vg_cast5_ofb_final`. -/
def ofbFinal : Prog isa := modeFn fun n => (dirCore true n).seqFinal (Modes.Mode.ofb 2)

end VG.Impl.Cast5.RISCV64
