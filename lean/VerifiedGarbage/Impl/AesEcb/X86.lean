module

public import VerifiedGarbage.Impl.Aes.X86.Callee
public import VerifiedGarbage.Impl.CallWipe.X86
public import VerifiedGarbage.Impl.Zeroize.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# AES-ECB on x86

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt`, for an implementation of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` that writes only the
first `n` bytes of `scratch` (the fifth of the five argument slots): its
code itself where `n = 0` (it writes nothing there), and otherwise a call of
it, then of `vg_zeroize`'s code (the internal `vg_zeroize_core`) on those
`n` bytes.
-/

@[expose] public section

namespace VG.Impl.AesEcb.X86

open VG.X86

/-- A call of the blocks function `b`, then of `vg_zeroize`'s code (the
internal `vg_zeroize_core`) on the first `n` bytes of `scratch`. -/
def wiped (b : Impl.Aes.X86.Blocks) (n : Nat) : Prog isa :=
  Impl.CallWipe.X86.callWipe 5 4 n b.name b.code "vg_zeroize_core" Impl.Zeroize.X86.zeroize

end VG.Impl.AesEcb.X86

/-! ## The functions as emitted

Each function, then its cleanup: for a block function that writes nothing
in `scratch` and calls nothing, its code and then the clearing of the
registers but the result (`Impl.Scrub.X86.scrub 0`); otherwise the call
wiping `scratch` (`wiped`), the zeroing of the 32 bytes of stack below `esp`
that it and its callees use, and that clearing (`Impl.Scrub.X86.scrubF 0 32`),
so that it returns without secret residue. -/

namespace VG.Impl.AesEcb.X86.Fn

open VG.X86
open VG.Impl.Aes.X86 (Blocks)

/-- `vg_aes_ecb_encrypt` or `vg_aes_ecb_decrypt` as the block function `b`
itself, as emitted. -/
def free (b : Blocks) : Prog isa := Impl.Scrub.X86.scrub 0 b.code

/-- `vg_aes_ecb_encrypt` or `vg_aes_ecb_decrypt` as the call of `b`, then of
`vg_zeroize` on the first `n` bytes of `scratch`, as emitted. -/
def wiped (b : Blocks) (n : Nat) : Prog isa := Impl.Scrub.X86.scrubF 0 32 (Impl.AesEcb.X86.wiped b n)

end VG.Impl.AesEcb.X86.Fn
