module

public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Impl.Modes.AArch64.Fb

/-!
# Single-block Camellia-OFB and Camellia-CFB128 on AArch64

The generic feedback modes use the serial Camellia core. Its Feistel halves
stay in scalar registers and its S-box stays in vector registers; it keeps
`x19`, where the modes retain the IV pointer. All table loads use fixed public
addresses, and secret indices select bytes only within vector registers.
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64

open VG.AArch64

/-- The single-block encryption core, preserving the IV pointer in `x19`. -/
abbrev fbCore : Impl.Modes.AArch64.Core := Serial.core

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa := fbCore.fb .ofb ⟨.x2, .x3, .x4, .x5⟩ .x19

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := fbCore.fb .cfbEnc ⟨.x2, .x3, .x4, .x5⟩ .x19

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa := fbCore.fb .cfbDec ⟨.x2, .x3, .x4, .x5⟩ .x19

end VG.Impl.Camellia.AArch64
