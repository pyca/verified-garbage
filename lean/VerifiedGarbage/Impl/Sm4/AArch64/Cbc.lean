module

public import VerifiedGarbage.Impl.Sm4.AArch64.Ctr
public import VerifiedGarbage.Impl.Modes.AArch64.Cbc
public import VerifiedGarbage.Impl.Modes.AArch64.CbcEnc

/-!
# SM4-CBC, bitsliced, on AArch64

`cbcEncrypt` and `cbcDecrypt(schedule = x0, iv = x1, data = x2, n = x3,
scratch = x4)`: `vg_sm4_cbc_encrypt` and `vg_sm4_cbc_decrypt`, the modes'
generic CBC (`Impl/Modes/AArch64/CbcEnc.lean`, `Cbc.lean`) over SM4's core
with its round keys in the order of each direction (`dirCore`). Decryption
transforms sixteen blocks at a time; encryption, which is sequential, one.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64

/-- `vg_sm4_cbc_encrypt`. -/
def cbcEncrypt : Prog isa := (dirCore .encrypt).cbcEncrypt ⟨.x1, .x2, .x3, .x4⟩

/-- `vg_sm4_cbc_decrypt`. -/
def cbcDecrypt : Prog isa := (dirCore .decrypt).cbcDecrypt ⟨.x1, .x2, .x3, .x4⟩

end VG.Impl.Sm4.AArch64
