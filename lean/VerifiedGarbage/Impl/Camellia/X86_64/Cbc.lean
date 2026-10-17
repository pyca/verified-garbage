module

public import VerifiedGarbage.Impl.Camellia.X86_64.Ctr
public import VerifiedGarbage.Impl.Modes.X86_64.CbcChained

/-!
# Camellia-CBC, bitsliced, on x86-64

`cbcEncryptChained` and `cbcDecryptChained(schedule = rdi, rounds = rsi,
iv = rdx, data = rcx, n = r8, scratch = r9)`: `vg_camellia_cbc_encrypt_chained`
and `vg_camellia_cbc_decrypt_chained`, the modes' generic CBC that updates
the chaining value (`Impl/Modes/X86_64/CbcChained.lean`) over Camellia's core with its
subkeys in the order of each direction (`dirCore`). Decryption transforms
eight blocks at a time; encryption, which is sequential, one.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86_64

open VG.X86_64

/-- `vg_camellia_cbc_encrypt_chained`. -/
def cbcEncryptChained : Prog isa := (dirCore .encrypt).cbcEncryptChained ⟨.rdx, .rcx, .r8, .r9⟩

/-- `vg_camellia_cbc_decrypt_chained`. -/
def cbcDecryptChained : Prog isa := (dirCore .decrypt).cbcDecryptChained ⟨.rdx, .rcx, .r8, .r9⟩

end VG.Impl.Camellia.X86_64
