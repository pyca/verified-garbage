module

public import VerifiedGarbage.Impl.Camellia.AArch64.Fb
public import VerifiedGarbage.Impl.Modes.AArch64.FbFinal

/-!
# Camellia-CFB128 and Camellia-OFB of a message's last piece on AArch64

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = x0, rounds = x1,
iv = x2, data = x3, len = x4, scratch = x5): the modes' CFB and OFB over a message's
last piece, of any length (`Impl/Modes/AArch64/FbFinal.lean`), over the
serial encryption core of `ofb` and `cfbEncrypt`, with their arguments but
the data's length in bytes, and the IV's address kept in `x19`, as there.
Decryption takes the serial core too: a call is a message's last piece.
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64

open VG.AArch64

/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := fbCore.fbFinal .cfbEnc ⟨.x2, .x3, .x4, .x5⟩ .x19

/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := fbCore.fbFinal .cfbDec ⟨.x2, .x3, .x4, .x5⟩ .x19

/-- `vg_camellia_ofb_final`. -/
def ofbFinal : Prog isa := fbCore.fbFinal .ofb ⟨.x2, .x3, .x4, .x5⟩ .x19

end VG.Impl.Camellia.AArch64
