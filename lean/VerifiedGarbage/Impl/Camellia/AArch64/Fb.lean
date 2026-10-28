module

public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Prepared
public import VerifiedGarbage.Impl.Modes.AArch64.Fb
public import VerifiedGarbage.Impl.Camellia.AArch64.Ctr
public import VerifiedGarbage.Impl.Modes.AArch64.CfbDec

/-!
# Camellia-OFB and Camellia-CFB128 on AArch64

OFB, CFB encryption and short CFB decryption use the serial Camellia core,
which they call (`Serial/Prepared.lean`): `vg_camellia_prepare_encrypt_keys`
once, `vg_camellia_encrypt_prepared` for each block. Its Feistel halves
stay in scalar registers and its S-box stays in vector registers; neither
function writes `x19`, where the modes retain the IV pointer. All table
loads use fixed public addresses, and secret indices select bytes only
within vector registers.
CFB decryption of at least eight blocks gathers preceding ciphertexts and
encrypts them in independent groups using the existing eight-block core.
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64

open VG.AArch64

/-- The single-block encryption core, calling the serial core's functions
and preserving the IV pointer in `x19`. -/
abbrev fbCore : Impl.Modes.AArch64.Core := Serial.callCore

/-- `vg_camellia_ofb`. -/
def ofb : Prog isa := fbCore.fb .ofb ⟨.x2, .x3, .x4, .x5⟩ .x19

/-- `vg_camellia_cfb128_encrypt`. -/
def cfbEncrypt : Prog isa := fbCore.fb .cfbEnc ⟨.x2, .x3, .x4, .x5⟩ .x19

/-- `vg_camellia_cfb128_decrypt`. -/
def cfbDecrypt : Prog isa :=
  .seq (.block [.lsr .x .x13 .x4 3])
    (.ite (.zero .x .x13)
      (fbCore.fb .cfbDec ⟨.x2, .x3, .x4, .x5⟩ .x19)
      (modeCore.cfbDecryptBatched ⟨.x2, .x3, .x4, .x5⟩))

end VG.Impl.Camellia.AArch64
