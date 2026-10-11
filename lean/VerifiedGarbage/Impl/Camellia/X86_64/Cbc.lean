module

public import VerifiedGarbage.Impl.Camellia.X86_64.Ctr
public import VerifiedGarbage.Impl.Modes.X86_64.Cbc
public import VerifiedGarbage.Impl.Modes.X86_64.CbcEnc

/-!
# Camellia-CBC, bitsliced, on x86-64

`cbcEncrypt` and `cbcDecrypt(schedule = rdi, rounds = rsi, iv = rdx,
data = rcx, n = r8, scratch = r9)`: `vg_camellia_cbc_encrypt` and
`vg_camellia_cbc_decrypt`, the modes' generic CBC
(`Impl/Modes/X86_64/CbcEnc.lean`, `Cbc.lean`) over Camellia's core with its
subkeys in the order of each direction (`dirCore`). Decryption transforms
eight blocks at a time; encryption, which is sequential, one.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86_64

open VG.X86_64

/-- `vg_camellia_cbc_encrypt`. -/
def cbcEncrypt : Prog isa := (dirCore .encrypt).cbcEncrypt ⟨.rdx, .rcx, .r8, .r9⟩

/-- `vg_camellia_cbc_decrypt`. -/
def cbcDecrypt : Prog isa := (dirCore .decrypt).cbcDecrypt ⟨.rdx, .rcx, .r8, .r9⟩

end VG.Impl.Camellia.X86_64
