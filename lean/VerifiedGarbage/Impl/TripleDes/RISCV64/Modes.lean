module

public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Ecb

/-!
# Triple DES's modes on RISC-V

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt`, `cfbDecrypt`,
`cfb8Encrypt` and `cfb8Decrypt` (schedule = a0, iv = a1, data = a2, n = a3)
are the modes (`Impl/Modes/RISCV64/Seq.lean`) over `dirCore` (`Ecb.lean`):
CBC in both directions, and the others with the encryption.
-/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64

open VG.RISCV64

/-- `vg_triple_des_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEncChained 2)

/-- `vg_triple_des_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).seq (Modes.Mode.cbcDecChained 2)

/-- `vg_triple_des_ofb`. -/
def ofb : Prog isa := (dirCore .encrypt).seq (Modes.Mode.ofb 2)

/-- `vg_triple_des_cfb64_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbEnc 2)

/-- `vg_triple_des_cfb64_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfbDec 2)

/-- `vg_triple_des_cfb8_encrypt`. -/
def cfb8Encrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfb8Enc 2)

/-- `vg_triple_des_cfb8_decrypt`. -/
def cfb8Decrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cfb8Dec 2)

end VG.Impl.TripleDes.RISCV64
