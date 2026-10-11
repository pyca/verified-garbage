import VerifiedGarbage.Impl.Camellia.X86_64.Ctr
import VerifiedGarbage.Impl.Modes.X86_64.Fb

/-!
# Camellia-OFB and Camellia-CFB128, bitsliced, on x86-64

`ofb`, `cfbEncrypt` and `cfbDecrypt` (schedule = rdi, rounds = rsi, iv =
rdx, data = rcx, n = r8, scratch = r9): `vg_camellia_ofb`,
`vg_camellia_cfb128_encrypt` and `vg_camellia_cfb128_decrypt`, the modes'
generic OFB and CFB (`Impl/Modes/X86_64/Fb.lean`) over Camellia's core with
its subkeys in encryption order (`dirCore .encrypt`). Each block's input
depends on the block before it, so each is enciphered alone, in a batch.
-/

namespace VG.Impl.Camellia.X86_64

open VG.X86_64

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa := (dirCore .encrypt).fb .ofb ⟨.rdx, .rcx, .r8, .r9⟩

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).fb .cfbEnc ⟨.rdx, .rcx, .r8, .r9⟩

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore .encrypt).fb .cfbDec ⟨.rdx, .rcx, .r8, .r9⟩

end VG.Impl.Camellia.X86_64
