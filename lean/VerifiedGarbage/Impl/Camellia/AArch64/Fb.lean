import VerifiedGarbage.Impl.Camellia.AArch64.Ctr
import VerifiedGarbage.Impl.Modes.AArch64.Fb

/-!
# Camellia-OFB and Camellia-CFB128, bitsliced, on AArch64

`ofb`, `cfbEncrypt` and `cfbDecrypt` (schedule = x0, rounds = x1, iv = x2,
data = x3, n = x4, scratch = x5): `vg_camellia_ofb`,
`vg_camellia_cfb128_encrypt` and `vg_camellia_cfb128_decrypt`, the modes'
generic OFB and CFB (`Impl/Modes/AArch64/Fb.lean`) over Camellia's core for
encryption (`modeCore`). The core writes every general-purpose register the
IV's address could be kept in, but no vector register: the modes keep it in
`x19` (a callee-saved register, which they restore), and `fbCore` keeps
`x19` in `v31` around the core's code (`Core.viaV`). Each block's input
depends on the block before it, so each is enciphered alone, in a batch of
eight.
-/

namespace VG.Impl.Camellia.AArch64

open VG.AArch64

/-- Camellia's core for the feedback modes: `x19` kept in `v31` around its
code. -/
abbrev fbCore : Impl.Modes.AArch64.Core := modeCore.viaV .x19 .v31

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa := fbCore.fb .ofb ⟨.x2, .x3, .x4, .x5⟩ .x19

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := fbCore.fb .cfbEnc ⟨.x2, .x3, .x4, .x5⟩ .x19

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := fbCore.fb .cfbDec ⟨.x2, .x3, .x4, .x5⟩ .x19

end VG.Impl.Camellia.AArch64
