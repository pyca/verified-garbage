module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Fb
public import VerifiedGarbage.Impl.Modes.AArch64.FbFinal

/-!
# Triple DES-CFB64 of a message's last piece on AArch64

`cfbEncryptFinal` and `cfbDecryptFinal` (schedule = x0, iv = x1,
data = x2, len = x3, scratch = x4): the modes' CFB over a message's last
piece, of any length (`Impl/Modes/AArch64/FbFinal.lean`), over CBC
encryption's core, with the arguments of `cfbEncrypt` but the data's length
in bytes, and the IV's address kept in `x25`, as there.
-/

@[expose] public section

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64

/-- `vg_triple_des_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt).fbFinal .cfbEnc fbRegs .x25

/-- `vg_triple_des_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt).fbFinal .cfbDec fbRegs .x25

end VG.Impl.TripleDes.AArch64
