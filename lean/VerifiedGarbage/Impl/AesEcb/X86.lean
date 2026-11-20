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

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` over a block function `b`
that writes the first `n` bytes of `scratch`, then their cleanup: where `b`
writes nothing in `scratch` and calls nothing (`free`), `b`'s code and then the
clearing of the registers but the result (`Impl.Scrub.X86.scrub 0`);
otherwise the call wiping `scratch` (`wiped`), the zeroing of the 32 bytes
of stack below `esp` that it and its callees use, and that clearing
(`Impl.Scrub.X86.scrubF 0 32`), so that it returns without secret
residue. -/

namespace VG.Impl.AesEcb.X86.Fn

open VG.X86
open VG.Impl.Aes.X86 (Blocks)

/-- `vg_aes_ecb_encrypt` or `vg_aes_ecb_decrypt` over the block function
`b`, which writes the first `n` bytes of `scratch`, as emitted: `b`'s own
code where `free` (it writes nothing in `scratch` and calls nothing), the
call wiping `scratch` otherwise. -/
def crypt (free : Bool) (b : Blocks) (n : Nat) : Prog isa :=
  if free then Impl.Scrub.X86.scrub 0 b.code
  else Impl.Scrub.X86.scrubF 0 32 (Impl.AesEcb.X86.wiped b n)

end VG.Impl.AesEcb.X86.Fn
