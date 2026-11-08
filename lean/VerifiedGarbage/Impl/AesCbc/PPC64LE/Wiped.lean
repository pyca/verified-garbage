module

public import VerifiedGarbage.Impl.AesCbc.PPC64LE
public import VerifiedGarbage.Impl.CallWipe.PPC64LE
public import VerifiedGarbage.Impl.Zeroize.PPC64LE

/-!
# AES-CBC on PPC64LE, zeroing its scratch

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt`: a call of the CBC code
(`Impl/AesCbc/PPC64LE.lean`, now the internal functions
`vg_aes_cbc_encrypt_unwiped` and `vg_aes_cbc_decrypt_unwiped`), then of
`vg_zeroize` on the 2176 bytes of `scratch` (the sixth argument, in `r8`),
which it may write.
-/

@[expose] public section

namespace VG.Impl.AesCbc.PPC64LE.Wiped

open VG.PPC64LE

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the 2176
bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.PPC64LE.callWipe 48 .r8 2176 name body "vg_zeroize" Impl.Zeroize.PPC64LE.zeroize

/-- `vg_aes_cbc_encrypt`. -/
def encrypt : Prog isa := wiped "vg_aes_cbc_encrypt_unwiped" Impl.AesCbc.PPC64LE.encrypt

/-- `vg_aes_cbc_decrypt`. -/
def decrypt : Prog isa := wiped "vg_aes_cbc_decrypt_unwiped" Impl.AesCbc.PPC64LE.decrypt

end VG.Impl.AesCbc.PPC64LE.Wiped
