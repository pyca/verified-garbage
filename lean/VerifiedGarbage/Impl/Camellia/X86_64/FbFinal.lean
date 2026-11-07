module

public import VerifiedGarbage.Impl.Camellia.X86_64.Fb
public import VerifiedGarbage.Impl.Modes.X86_64.FbFinal

/-!
# Camellia-CFB128 and Camellia-OFB of a message's last piece on x86-64

`cfbEncryptFinal`, `cfbDecryptFinal` and `ofbFinal` (schedule = rdi, rounds =
rsi, iv = rdx, data = rcx, len = r8, scratch = r9): the modes' CFB and OFB
over a message's last piece, of any length (`Impl/Modes/X86_64/FbFinal.lean`),
over Camellia's core, with the arguments of `cfbEncrypt` (and `ofb`) but the
data's length in bytes.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86_64

open VG.X86_64

/-- `vg_camellia_cfb128_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (dirCore .encrypt).fbFinal .cfbEnc ⟨.rdx, .rcx, .r8, .r9⟩

/-- `vg_camellia_cfb128_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (dirCore .encrypt).fbFinal .cfbDec ⟨.rdx, .rcx, .r8, .r9⟩

/-- `vg_camellia_ofb_final`. -/
def ofbFinal : Prog isa := (dirCore .encrypt).fbFinal .ofb ⟨.rdx, .rcx, .r8, .r9⟩

end VG.Impl.Camellia.X86_64
