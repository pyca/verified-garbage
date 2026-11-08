module

public import VerifiedGarbage.Impl.Aes.X86.Callee
public import VerifiedGarbage.Impl.CallWipe.X86
public import VerifiedGarbage.Impl.Zeroize.X86

/-!
# AES-ECB on x86

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt`, for an implementation of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`: a call of it, then of
`vg_zeroize` on the 2048 bytes of `scratch` (the fifth of the five argument
slots), which it may write.
-/

@[expose] public section

namespace VG.Impl.AesEcb.X86

open VG.X86

/-- A call of the blocks function `b`, then of `vg_zeroize` on the 2048
bytes of `scratch`. -/
def wiped (b : Impl.Aes.X86.Blocks) : Prog isa :=
  Impl.CallWipe.X86.callWipe 5 4 2048 b.name b.code "vg_zeroize" Impl.Zeroize.X86.zeroize

end VG.Impl.AesEcb.X86
