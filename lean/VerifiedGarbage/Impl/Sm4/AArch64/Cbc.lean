module

public import VerifiedGarbage.Impl.Sm4.AArch64.Fb
public import VerifiedGarbage.Impl.Modes.AArch64.CbcChained

/-!
# SM4-CBC, bitsliced, on AArch64

`cbcEncryptChained` and `cbcDecryptChained(schedule = x0, iv = x1,
data = x2, n = x3, scratch = x4)`: `vg_sm4_cbc_encrypt_chained` and
`vg_sm4_cbc_decrypt_chained`, the modes' generic CBC that updates the
chaining value (`Impl/Modes/AArch64/CbcChained.lean`) over SM4's core with
its round keys in the order of each direction (`dirCore`). Decryption
transforms sixteen blocks at a time; encryption, which is sequential, one,
with the IV's address in `x19`, which the core keeps in `v31` (`fbCore`, as
for OFB and CFB).
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64

/-- `vg_sm4_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := fbCore.cbcEncryptChained ⟨.x1, .x2, .x3, .x4⟩ .x19

/-- `vg_sm4_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).cbcDecryptChained ⟨.x1, .x2, .x3, .x4⟩

end VG.Impl.Sm4.AArch64
