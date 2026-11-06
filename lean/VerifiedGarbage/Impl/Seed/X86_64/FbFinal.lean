module

public import VerifiedGarbage.Impl.Seed.X86_64.Modes
public import VerifiedGarbage.Impl.Modes.X86_64.FbFinal

/-!
# SEED-CFB128 of a message's last piece on x86-64

`cfbEncryptFinal` and `cfbDecryptFinal`: the modes' CFB over a message's
last piece, of any length (`Impl/Modes/X86_64/FbFinal.lean`), over
SEED's core, with the arguments of `cfbEncrypt` but the data's length
in bytes.
-/

@[expose] public section

namespace VG.Impl.Seed.X86_64

open VG.X86_64

/-- `vg_seed_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt).fbFinal .cfbEnc modeRegs

/-- `vg_seed_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt).fbFinal .cfbDec modeRegs

end VG.Impl.Seed.X86_64
