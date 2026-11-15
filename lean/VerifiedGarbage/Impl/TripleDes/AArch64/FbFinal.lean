module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Fb
public import VerifiedGarbage.Impl.Modes.AArch64.FbFinal

/-!
# Triple DES-CFB64 and Triple DES-OFB of a message's last piece on AArch64

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = x0, iv = x1,
data = x2, len = x3, scratch = x4): the modes' CFB and OFB over a message's last
piece, of any length (`Impl/Modes/AArch64/FbFinal.lean`), over the table
core, with the arguments of `cfbEncrypt` but the data's length in bytes,
and the IV's address kept in `x28`, as there.
-/

@[expose] public section

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64

/-- `vg_triple_des_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := tableCore.fbFinal .cfbEnc fbRegs .x28

/-- `vg_triple_des_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := tableCore.fbFinal .cfbDec fbRegs .x28

/-- `vg_triple_des_ofb_final`. -/
def ofbFinal : Prog isa := tableCore.fbFinal .ofb fbRegs .x28

end VG.Impl.TripleDes.AArch64
