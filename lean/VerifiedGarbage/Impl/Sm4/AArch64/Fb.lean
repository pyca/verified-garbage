import VerifiedGarbage.Impl.Sm4.AArch64.Ctr
import VerifiedGarbage.Impl.Modes.AArch64.Fb

/-!
# SM4-OFB and SM4-CFB128, bitsliced, on AArch64

`ofb`, `cfbEncrypt` and `cfbDecrypt` (schedule = x0, iv = x1, data = x2,
n = x3, scratch = x4): `vg_sm4_ofb`, `vg_sm4_cfb128_encrypt` and
`vg_sm4_cfb128_decrypt`, the modes' generic OFB and CFB
(`Impl/Modes/AArch64/Fb.lean`) over SM4's core with its round keys in
encryption order (`modeCore`). The core writes every general-purpose
register the IV's address could be kept in, but no vector register: the
modes keep it in `x19` (a callee-saved register, which they restore), and
`fbCore` keeps `x19` in `v31` around the core's code (`Core.viaV`). Each
block's input depends on the block before it, so each is enciphered alone,
in a batch of sixteen.
-/

namespace VG.Impl.Sm4.AArch64

open VG.AArch64

/-- SM4's core for the feedback modes: `x19` kept in `v31` around its code. -/
abbrev fbCore : Impl.Modes.AArch64.Core := modeCore.viaV .x19 .v31

/-- `vg_sm4_ofb`. -/
def ofb : Prog isa := fbCore.fb .ofb ⟨.x1, .x2, .x3, .x4⟩ .x19

/-- `vg_sm4_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := fbCore.fb .cfbEnc ⟨.x1, .x2, .x3, .x4⟩ .x19

/-- `vg_sm4_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := fbCore.fb .cfbDec ⟨.x1, .x2, .x3, .x4⟩ .x19

end VG.Impl.Sm4.AArch64
