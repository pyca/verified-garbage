module

public import VerifiedGarbage.Impl.Camellia.AArch64.Ctr
public import VerifiedGarbage.Impl.Modes.AArch64.Cbc
public import VerifiedGarbage.Impl.Modes.AArch64.CbcEnc

/-!
# Camellia-CBC, bitsliced, on AArch64

`cbcEncrypt` and `cbcDecrypt(schedule = x0, rounds = x1, iv = x2, data = x3,
n = x4, scratch = x5)`: `vg_camellia_cbc_encrypt` and
`vg_camellia_cbc_decrypt`, the modes' generic CBC
(`Impl/Modes/AArch64/CbcEnc.lean`, `Cbc.lean`) over Camellia's core with
its subkeys in the order of each direction (`dirCore`). Decryption
transforms eight blocks at a time; encryption, which is sequential, one.
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64

open VG.AArch64

/-- `vg_camellia_cbc_encrypt`. -/
def cbcEncrypt : Prog isa := (dirCore .encrypt).cbcEncrypt ⟨.x2, .x3, .x4, .x5⟩

/-- `vg_camellia_cbc_decrypt`. -/
def cbcDecrypt : Prog isa := (dirCore .decrypt).cbcDecrypt ⟨.x2, .x3, .x4, .x5⟩

end VG.Impl.Camellia.AArch64
