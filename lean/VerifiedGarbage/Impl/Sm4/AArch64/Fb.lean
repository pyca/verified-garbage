module

public import VerifiedGarbage.Impl.Sm4.AArch64.Ctr
public import VerifiedGarbage.Impl.Modes.AArch64.Fb
public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Core
public import VerifiedGarbage.Impl.Modes.AArch64.CfbDec

/-! # SM4 feedback modes with a serial core and independent decryption batches

OFB and CFB encryption follow a dependent chain, using the existing serial
SM4 core with a register-resident S-box. CFB decryption gathers preceding
original ciphertexts and encrypts them in sixteen-block batches; inputs
shorter than eight blocks use the serial core. The modes retain the existing
scratch layout, IV update, framing and zeroization.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64

/-- The serial core naturally preserves the IV pointer in `x19`. -/
abbrev fbCore : Impl.Modes.AArch64.Core := Serial.core

/-- `vg_sm4_ofb`. -/
def ofb : Prog isa := fbCore.fb .ofb ⟨.x1, .x2, .x3, .x4⟩ .x19

/-- `vg_sm4_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := fbCore.fb .cfbEnc ⟨.x1, .x2, .x3, .x4⟩ .x19

/-- `vg_sm4_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa :=
  .seq (.block [.lsr .x .x13 .x3 3])
    (.ite (.zero .x .x13)
      (fbCore.fb .cfbDec ⟨.x1, .x2, .x3, .x4⟩ .x19)
      (modeCore.cfbDecryptBatched ⟨.x1, .x2, .x3, .x4⟩))

end VG.Impl.Sm4.AArch64
