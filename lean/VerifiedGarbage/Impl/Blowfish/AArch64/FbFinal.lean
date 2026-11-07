module

public import VerifiedGarbage.Impl.Blowfish.AArch64.Modes
public import VerifiedGarbage.Impl.Modes.AArch64.FbFinal

/-!
# Blowfish-CFB64 and Blowfish-OFB of a message's last piece on AArch64

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = x0,
iv = x1, data = x2, len = x3, scratch = x4): the modes' CFB and OFB over a
message's last piece, of any length (`Impl/Modes/AArch64/FbFinal.lean`),
over Blowfish's encryption core, with the arguments of `cfbEncrypt` (and
`ofb`) but the data's length in bytes, and the IV's address kept in `x25`,
as there.
-/

@[expose] public section

namespace VG.Impl.Blowfish.AArch64

open VG.AArch64

/-- `vg_blowfish_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore true).fbFinal .cfbEnc modeRegs .x25

/-- `vg_blowfish_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore true).fbFinal .cfbDec modeRegs .x25

/-- `vg_blowfish_ofb_final`. -/
def ofbFinal : Prog isa := (dirCore true).fbFinal .ofb modeRegs .x25

end VG.Impl.Blowfish.AArch64
