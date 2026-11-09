module

public import VerifiedGarbage.Impl.Idea.X86.Modes
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal

/-!
# IDEA-CFB64 and IDEA-OFB of a message's last piece on x86 (32-bit)

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (cdecl: schedule, iv, data, len,
scratch): the modes' CFB and OFB over a message's last piece, of any length
(`Impl/Modes/X86/SeqFinal.lean`), over IDEA's core, with the arguments of
`cfbEncrypt` but the data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Idea.X86

open VG.X86

/-- `vg_idea_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := modeCore.seqFinal (Modes.Mode.cfbEnc 2)

/-- `vg_idea_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := modeCore.seqFinal (Modes.Mode.cfbDec 2)

/-- `vg_idea_ofb_final`. -/
def ofbFinal : Prog isa := modeCore.seqFinal (Modes.Mode.ofb 2)

end VG.Impl.Idea.X86
