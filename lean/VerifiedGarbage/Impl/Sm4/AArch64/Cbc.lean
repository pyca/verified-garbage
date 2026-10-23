module

public import VerifiedGarbage.Impl.Sm4.AArch64.Fb
public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Core
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained

/-!
# SM4-CBC on AArch64

`cbcEncryptChained` and `cbcDecryptChained(schedule = x0, iv = x1,
data = x2, n = x3, scratch = x4)`: `vg_sm4_cbc_encrypt_chained` and
`vg_sm4_cbc_decrypt_chained`, the modes' generic CBC that updates the
chaining value (`Impl/Modes/AArch64/CbcChained.lean`). Decryption uses the
bitsliced core and transforms sixteen blocks at a time. Encryption uses
`Serial.Core`: one block under the raw schedule, with the S-box held in
vector registers. Both keep the IV address in `x19`.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64

/-- `vg_sm4_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := Serial.cbcEncryptChained

/-- `vg_sm4_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).cbcDecryptChained ⟨.x1, .x2, .x3, .x4⟩

end VG.Impl.Sm4.AArch64
