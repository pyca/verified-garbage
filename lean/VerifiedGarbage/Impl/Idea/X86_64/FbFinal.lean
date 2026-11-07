module

public import VerifiedGarbage.Impl.Idea.X86_64.Modes
public import VerifiedGarbage.Impl.Modes.X86_64.FbFinal

/-!
# IDEA-CFB64 and IDEA-OFB of a message's last piece on x86-64

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = rdi, iv = rsi,
data = rdx, len = rcx, scratch = r8): the modes' CFB and OFB over a message's
last piece, of any length (`Impl/Modes/X86_64/FbFinal.lean`), over IDEA's
core, with the arguments of `cfbEncrypt` (and `ofb`) but the data's length in
bytes.
-/

@[expose] public section

namespace VG.Impl.Idea.X86_64

open VG.X86_64

/-- `vg_idea_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := modeCore.fbFinal .cfbEnc modeRegs

/-- `vg_idea_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := modeCore.fbFinal .cfbDec modeRegs

/-- `vg_idea_ofb_final`. -/
def ofbFinal : Prog isa := modeCore.fbFinal .ofb modeRegs

end VG.Impl.Idea.X86_64
