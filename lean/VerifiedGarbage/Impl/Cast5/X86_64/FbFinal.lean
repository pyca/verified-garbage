module

public import VerifiedGarbage.Impl.Cast5.X86_64.Modes
public import VerifiedGarbage.Impl.Modes.X86_64.FbFinal

/-!
# CAST5-CFB64 and CAST5-OFB of a message's last piece on x86-64

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = rdi, rounds =
rsi, iv = rdx, data = rcx, len = r8, scratch = r9): the modes' CFB and OFB
over a message's last piece, of any length (`Impl/Modes/X86_64/FbFinal.lean`),
over CAST5's core, with the arguments of `cfbEncrypt` (and `ofb`) but the
data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Cast5.X86_64

open VG.X86_64

/-- `vg_cast5_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore true).fbFinal .cfbEnc modeRegs

/-- `vg_cast5_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore true).fbFinal .cfbDec modeRegs

/-- `vg_cast5_ofb_final`. -/
def ofbFinal : Prog isa := (dirCore true).fbFinal .ofb modeRegs

end VG.Impl.Cast5.X86_64
