module

public import VerifiedGarbage.Impl.TripleDes.X86_64.Fb
public import VerifiedGarbage.Impl.Modes.X86_64.FbFinal

/-!
# Triple DES-CFB64 of a message's last piece on x86-64

`cfbEncryptFinal` and `cfbDecryptFinal`: the modes' CFB over a message's
last piece, of any length (`Impl/Modes/X86_64/FbFinal.lean`), over
CBC encryption's core (`callCore .encrypt`, calling the block function), with the arguments of `cfbEncrypt` but the data's length
in bytes.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86_64

open VG.X86_64

/-- `vg_triple_des_cfb64_encrypt_final`. -/
def cfbEncryptFinal : Prog isa := (callCore .encrypt).fbFinal .cfbEnc fbRegs

/-- `cfbEncryptFinal` with the block function inlined. -/
def cfbEncryptFinalI : Prog isa := (dirCore .encrypt).fbFinal .cfbEnc fbRegs

/-- `vg_triple_des_cfb64_decrypt_final`. -/
def cfbDecryptFinal : Prog isa := (callCore .encrypt).fbFinal .cfbDec fbRegs

/-- `cfbDecryptFinal` with the block function inlined. -/
def cfbDecryptFinalI : Prog isa := (dirCore .encrypt).fbFinal .cfbDec fbRegs

end VG.Impl.TripleDes.X86_64
