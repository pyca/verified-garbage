module

public import VerifiedGarbage.Impl.Sm4.X86_64.Ctr
public import VerifiedGarbage.Impl.Modes.X86_64.Cbc
public import VerifiedGarbage.Impl.Modes.X86_64.CbcEnc

/-!
# SM4-CBC, bitsliced, on x86-64

`cbcEncrypt` and `cbcDecrypt(schedule = rdi, iv = rsi, data = rdx, n = rcx,
scratch = r8)`: `vg_sm4_cbc_encrypt` and `vg_sm4_cbc_decrypt`, the modes'
generic CBC (`Impl/Modes/X86_64/CbcEnc.lean`, `Cbc.lean`) over SM4's core
with its round keys in the order of each direction (`dirCore`). Decryption
transforms sixteen blocks at a time; encryption, which is sequential, one.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86_64

open VG.X86_64

/-- `vg_sm4_cbc_encrypt`. -/
def cbcEncrypt : Prog isa := (dirCore .encrypt).cbcEncrypt ⟨.rsi, .rdx, .rcx, .r8⟩

/-- `vg_sm4_cbc_decrypt`. -/
def cbcDecrypt : Prog isa := (dirCore .decrypt).cbcDecrypt ⟨.rsi, .rdx, .rcx, .r8⟩

end VG.Impl.Sm4.X86_64
