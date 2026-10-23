module

public import VerifiedGarbage.Impl.Camellia.AArch64.Fb
public import VerifiedGarbage.Impl.Camellia.AArch64.Ctr
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained

/-!
# Camellia-CBC on AArch64

`cbcEncryptChained` and `cbcDecryptChained(schedule = x0, rounds = x1, iv = x2, data = x3,
n = x4, scratch = x5)`: `vg_camellia_cbc_encrypt_chained` and
`vg_camellia_cbc_decrypt_chained`, the modes' generic CBC that updates the
chaining value (`Impl/Modes/AArch64/CbcChained.lean`) over Camellia's core
with its subkeys in the order of each direction (`dirCore`). Decryption
transforms eight blocks at a time; encryption, which is sequential, one,
using the serial register-table core and retaining the IV address in `x19`
(`fbCore`, as for OFB and CFB).
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64

open VG.AArch64

/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := fbCore.cbcEncryptChained ⟨.x2, .x3, .x4, .x5⟩ .x19

/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).cbcDecryptChained ⟨.x2, .x3, .x4, .x5⟩

end VG.Impl.Camellia.AArch64
