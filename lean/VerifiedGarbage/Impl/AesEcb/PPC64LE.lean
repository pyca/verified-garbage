module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Blocks
public import VerifiedGarbage.Impl.CallWipe.PPC64LE
public import VerifiedGarbage.Impl.Zeroize.PPC64LE

/-!
# AES-ECB on PPC64LE

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt`: a call of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`, then of `vg_zeroize` on
the 2048 bytes of `scratch` (the fifth argument, in `r7`), which the blocks
functions may write.
-/

@[expose] public section

namespace VG.Impl.AesEcb.PPC64LE

open VG.PPC64LE

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the 2048
bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.PPC64LE.callWipe .r7 2048 name body "vg_zeroize" Impl.Zeroize.PPC64LE.zeroize

/-- `vg_aes_ecb_encrypt`. -/
def encrypt : Prog isa := wiped "vg_aes_encrypt_blocks" Impl.Aes.PPC64LE.encryptBlocks

/-- `vg_aes_ecb_decrypt`. -/
def decrypt : Prog isa := wiped "vg_aes_decrypt_blocks" Impl.Aes.PPC64LE.decryptBlocks

end VG.Impl.AesEcb.PPC64LE
