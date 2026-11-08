module

public import VerifiedGarbage.Impl.AesCbc.X86
public import VerifiedGarbage.Impl.CallWipe.X86
public import VerifiedGarbage.Impl.Zeroize.X86

/-!
# AES-CBC on x86, zeroing its scratch

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` for a blocks implementation
`b`: a call of the CBC code around `b` (`Impl/AesCbc/X86.lean`, now the
internal functions `vg_aes_cbc_encrypt_unwiped` and
`vg_aes_cbc_decrypt_unwiped`, with the variant's suffix), then of
`vg_zeroize` on the 2176 bytes of `scratch` (the sixth argument), which it
may write.
-/

@[expose] public section

namespace VG.Impl.AesCbc.X86.Wiped

open VG.X86
open VG.Impl.Aes.X86 (Blocks)

/-- A call of `name`, whose code is `body`, with the six stack arguments,
then of `vg_zeroize` on the 2176 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.X86.callWipe 6 5 2176 name body "vg_zeroize" Impl.Zeroize.X86.zeroize

/-- `vg_aes_cbc_encrypt` around `b`, whose variant's suffix is `suffix`. -/
def encrypt (b : Blocks) (suffix : String) : Prog isa :=
  wiped ("vg_aes_cbc_encrypt_unwiped" ++ suffix) (Impl.AesCbc.X86.encrypt b)

/-- `vg_aes_cbc_decrypt` around `b`, whose variant's suffix is `suffix`. -/
def decrypt (b : Blocks) (suffix : String) : Prog isa :=
  wiped ("vg_aes_cbc_decrypt_unwiped" ++ suffix) (Impl.AesCbc.X86.decrypt b)

end VG.Impl.AesCbc.X86.Wiped
