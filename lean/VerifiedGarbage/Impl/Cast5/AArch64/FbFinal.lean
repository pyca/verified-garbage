module

public import VerifiedGarbage.Impl.Cast5.AArch64.Modes
public import VerifiedGarbage.Impl.Modes.AArch64.FbFinal

/-!
# CAST5-CFB64 of a message's last piece on AArch64

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = x0, rounds = x1,
iv = x2, data = x3, len = x4, scratch = x5): the modes' CFB over a message's
last piece, of any length (`Impl/Modes/AArch64/FbFinal.lean`), over CAST5's
encryption core, with the arguments of `cfbEncrypt` but the data's length
in bytes, and the IV's address kept in `x25`, as there.
-/

@[expose] public section

namespace VG.Impl.Cast5.AArch64

open VG.AArch64

/-- `vg_cast5_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore true).fbFinal .cfbEnc modeRegs .x25

/-- `vg_cast5_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore true).fbFinal .cfbDec modeRegs .x25

end VG.Impl.Cast5.AArch64
