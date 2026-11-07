module

public import VerifiedGarbage.Impl.Seed.AArch64.Modes
public import VerifiedGarbage.Impl.Modes.AArch64.FbFinal

/-!
# SEED-CFB128 and SEED-OFB of a message's last piece on AArch64

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = x0, iv = x1,
data = x2, len = x3, scratch = x4): the modes' CFB and OFB over a message's last
piece, of any length (`Impl/Modes/AArch64/FbFinal.lean`), over SEED
encryption's core, with the arguments of `cfbEncrypt` but the data's length
in bytes, and the IV's address kept in `x25` (in `v31` around the core), as
there.
-/

@[expose] public section

namespace VG.Impl.Seed.AArch64

open VG.AArch64

/-- `vg_seed_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := fbCore.fbFinal .cfbEnc modeRegs .x25

/-- `vg_seed_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := fbCore.fbFinal .cfbDec modeRegs .x25

/-- `vg_seed_ofb_final`. -/
def ofbFinal : Prog isa := fbCore.fbFinal .ofb modeRegs .x25

end VG.Impl.Seed.AArch64
