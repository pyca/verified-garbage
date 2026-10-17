module

public import VerifiedGarbage.Impl.Sm4.X86_64.Ctr
public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained

/-!
# SM4-CBC, bitsliced, on x86-64

`cbcEncryptChained` and `cbcDecryptChained(schedule = rdi, iv = rsi,
data = rdx, n = rcx, scratch = r8)`: `vg_sm4_cbc_encrypt_chained` and
`vg_sm4_cbc_decrypt_chained`, the modes' generic CBC that updates the
chaining value (`Impl/Modes/X86_64/CbcChained.lean`) over SM4's core with
its round keys in the order of each direction (`dirCore`). Decryption
transforms sixteen blocks at a time; encryption, which is sequential, one.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86_64

open VG.X86_64

/-- `vg_sm4_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).cbcEncryptChained ⟨.rsi, .rdx, .rcx, .r8⟩

/-- `vg_sm4_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).cbcDecryptChained ⟨.rsi, .rdx, .rcx, .r8⟩

end VG.Impl.Sm4.X86_64
