module

public import VerifiedGarbage.Impl.Aes.X86_64.Callee
public import VerifiedGarbage.Impl.CallWipe.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AES-ECB on x86-64: the functions as emitted

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt`: an implementation of the
block function itself, where it writes no scratch space (`plain`), or its
call followed by the zeroing of the `n` bytes of `scratch` it writes
(`wiped`); then their cleanup (`Impl.Scrub.X86_64.scrubAll v 0 n`): every
vector register at the level `v` and every caller-saved register cleared,
and their whole stack wiped.
-/

@[expose] public section

namespace VG.Impl.AesEcb.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- The block function `b` alone, as emitted. -/
def plain (v : VecLevel) (b : Impl.Aes.X86_64.Blocks) : Prog isa :=
  scrubAll v 0 0 b.code

/-- The block function `b`, then the zeroing of the `n` bytes of `scratch`
it writes with `vg_zeroize`'s code `zCode`, named `zName`, as emitted. -/
def wiped (v : VecLevel) (n : Nat) (b : Impl.Aes.X86_64.Blocks) (zName : String) (zCode : Prog isa) :
    Prog isa :=
  scrubAll v 0 24 (Impl.CallWipe.X86_64.callWipe .r8 n b.name b.code zName zCode)

end VG.Impl.AesEcb.X86_64.Fn
