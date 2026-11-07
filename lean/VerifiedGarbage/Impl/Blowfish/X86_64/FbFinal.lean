module

public import VerifiedGarbage.Impl.Blowfish.X86_64.Modes
public import VerifiedGarbage.Impl.Modes.X86_64.FbFinal

/-!
# Blowfish-CFB64 of a message's last piece on x86-64

`cfbEncryptFinal` and `cfbDecryptFinal`: the modes' CFB over a message's
last piece, of any length (`Impl/Modes/X86_64/FbFinal.lean`), over
Blowfish's core, with the arguments of `cfbEncrypt` but the data's length
in bytes.
-/

@[expose] public section

namespace VG.Impl.Blowfish.X86_64

open VG.X86_64

/-- `vg_blowfish_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore true).fbFinal .cfbEnc modeRegs

/-- `vg_blowfish_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore true).fbFinal .cfbDec modeRegs

end VG.Impl.Blowfish.X86_64
