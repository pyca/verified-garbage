module

public import VerifiedGarbage.Impl.Sm4.X86_64.Fb
public import VerifiedGarbage.Impl.Modes.X86_64.FbFinal

/-!
# SM4-CFB128 and SM4-OFB of a message's last piece on x86-64

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal`: the modes' CFB and OFB
over a message's last piece, of any length (`Impl/Modes/X86_64/FbFinal.lean`),
over SM4's core, with the arguments of `cfbEncrypt` (and `ofb`) but the data's
length in bytes.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86_64

open VG.X86_64

/-- `vg_sm4_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt).fbFinal .cfbEnc ⟨.rsi, .rdx, .rcx, .r8⟩

/-- `vg_sm4_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt).fbFinal .cfbDec ⟨.rsi, .rdx, .rcx, .r8⟩

/-- `vg_sm4_ofb_final`. -/
def ofbFinal : Prog isa := (dirCore .encrypt).fbFinal .ofb ⟨.rsi, .rdx, .rcx, .r8⟩

end VG.Impl.Sm4.X86_64
