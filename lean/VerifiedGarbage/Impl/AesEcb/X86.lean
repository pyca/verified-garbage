module

public import VerifiedGarbage.Impl.Aes.X86.Callee
public import VerifiedGarbage.Impl.CallWipe.X86
public import VerifiedGarbage.Impl.Zeroize.X86

/-!
# AES-ECB on x86

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt`, for an implementation of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` that writes only the
first `n` bytes of `scratch` (the fifth of the five argument slots): its
code itself where `n = 0` (it writes nothing there), and otherwise a call of
it, then of `vg_zeroize` on those `n` bytes.
-/

@[expose] public section

namespace VG.Impl.AesEcb.X86

open VG.X86

/-- A call of the blocks function `b`, then of `vg_zeroize` on the first
`n` bytes of `scratch`. -/
def wiped (b : Impl.Aes.X86.Blocks) (n : Nat) : Prog isa :=
  Impl.CallWipe.X86.callWipe 5 4 n b.name b.code "vg_zeroize" Impl.Zeroize.X86.zeroize

end VG.Impl.AesEcb.X86
