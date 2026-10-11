import VerifiedGarbage.Impl.Sm4.X86_64.Ctr
import VerifiedGarbage.Impl.Modes.X86_64.Fb

/-!
# SM4-OFB and SM4-CFB128, bitsliced, on x86-64

`ofb`, `cfbEncrypt` and `cfbDecrypt` (schedule = rdi, iv = rsi, data = rdx,
n = rcx, scratch = r8): `vg_sm4_ofb`, `vg_sm4_cfb128_encrypt` and
`vg_sm4_cfb128_decrypt`, the modes' generic OFB and CFB
(`Impl/Modes/X86_64/Fb.lean`) over SM4's core with its round keys in
encryption order (`dirCore .encrypt`). Each block's input depends on the
block before it, so each is enciphered alone, in a batch of sixteen.
-/

namespace VG.Impl.Sm4.X86_64

open VG.X86_64

/-- `vg_sm4_ofb`. -/
def ofb : Prog isa := (dirCore .encrypt).fb .ofb ⟨.rsi, .rdx, .rcx, .r8⟩

/-- `vg_sm4_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := (dirCore .encrypt).fb .cfbEnc ⟨.rsi, .rdx, .rcx, .r8⟩

/-- `vg_sm4_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := (dirCore .encrypt).fb .cfbDec ⟨.rsi, .rdx, .rcx, .r8⟩

end VG.Impl.Sm4.X86_64
