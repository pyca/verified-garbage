module

public import VerifiedGarbage.Impl.AesCbc.X86_64
public import VerifiedGarbage.Impl.AesCbc.X86_64.Encrypt
public import VerifiedGarbage.Impl.AesCbc.X86_64.Decrypt
public import VerifiedGarbage.Impl.AesCbc.X86_64.VaesDecrypt
public import VerifiedGarbage.Impl.AesCbc.X86_64.Vaes512Decrypt
public import VerifiedGarbage.Impl.CallWipe.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AES-CBC on x86-64: the functions as emitted

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt`: the loop in AES-NI or VAES
registers where the implementation of the block functions has them
(`hw`, `vaes`), else the loop over its block function; called and then
followed by the zeroing of the bytes of `scratch` it may write with
`vg_zeroize`'s code `zCode`, named `zName`; then their cleanup
(`Impl.Scrub.X86_64.scrubAll v 0 n`): every vector register at the level
`v` and every caller-saved register cleared, and their whole stack wiped.
-/

@[expose] public section

namespace VG.Impl.AesCbc.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- The encryption loop. -/
def encBody (hw : Bool) (enc : Impl.Aes.X86_64.Blocks) : Prog isa :=
  if hw then Impl.AesCbc.X86_64.Encrypt.encrypt else Impl.AesCbc.X86_64.encrypt enc

/-- The decryption loop. -/
def decBody (vaes hw : Bool) (dec : Impl.Aes.X86_64.Blocks) : Prog isa :=
  if vaes then Impl.AesCbc.X86_64.VaesDecrypt.decrypt
  else if hw then Impl.AesCbc.X86_64.Decrypt.decrypt else Impl.AesCbc.X86_64.decrypt dec

/-- The level of the vector instructions of the decryption loop's own code:
the VAES loop's, else none above the implementation's. -/
def decLevel (vaes : Bool) : VecLevel := if vaes then .avx else .sse

/-- The bytes of `scratch` the decryption loop may write. -/
def decWrites (vaes hw : Bool) : Nat := if vaes then 224 else if hw then 224 else 2176

/-- `vg_aes_cbc_encrypt` as the loop in AES-NI registers alone, which writes
no scratch space, as emitted. -/
def encryptFree (v : VecLevel) : Prog isa := scrubAll v 0 0 Impl.AesCbc.X86_64.Encrypt.encrypt

/-- `vg_aes_cbc_encrypt`, its loop's scratch space zeroed, as emitted. -/
def encrypt (v : VecLevel) (hw : Bool) (enc : Impl.Aes.X86_64.Blocks) (sfx zName : String) (zCode : Prog isa) :
    Prog isa :=
  scrubAll v 0 32
    (Impl.CallWipe.X86_64.callWipe .r9 2176 ("vg_aes_cbc_encrypt_unwiped" ++ sfx) (encBody hw enc) zName zCode)

/-- `vg_aes_cbc_decrypt`, its loop's scratch space zeroed, as emitted. -/
def decrypt (v : VecLevel) (vaes hw : Bool) (dec : Impl.Aes.X86_64.Blocks) (sfx zName : String)
    (zCode : Prog isa) : Prog isa :=
  scrubAll v 0 32
    (Impl.CallWipe.X86_64.callWipe .r9 (decWrites vaes hw) ("vg_aes_cbc_decrypt_unwiped" ++ sfx)
      (decBody vaes hw dec) zName zCode)

/-- `vg_aes_cbc_decrypt_vaes_avx512`, as emitted. -/
def decryptVaes512 (v : VecLevel) (zName : String) (zCode : Prog isa) : Prog isa :=
  scrubAll v 0 32
    (Impl.CallWipe.X86_64.callWipe .r9 224 "vg_aes_cbc_decrypt_unwiped_vaes_avx512"
      Impl.AesCbc.X86_64.Vaes512Decrypt.decrypt zName zCode)

end VG.Impl.AesCbc.X86_64.Fn
