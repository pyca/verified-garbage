module

public import VerifiedGarbage.Impl.SlhDsa.AArch64.Shake
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Verify
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub

/-! # SLH-DSA (SHAKE) on AArch64: the functions as emitted

`vg_slhdsa_shake_*_keygen` of the parameter set `p` over the functions `f`
it calls, then its cleanup (`Impl.Scrub.AArch64.scrubAll`): every register
the calling convention does not preserve cleared (`Clear.all`), `x0` with
them as it returns nothing; it uses no stack (its calls, `bl`, store
nothing there). `vg_slhdsa_shake_*_sign` and `vg_slhdsa_shake_*_verify`
likewise, but for the 32 bits of their result, with the 16 bytes below the
stack pointer, the frame of the sponge functions they call, zeroed.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.AArch64.Fn

open VG.AArch64
open VG.Impl.Scrub.AArch64 (scrubAll Clear)

/-- `vg_slhdsa_shake_*_keygen`, as emitted. -/
def keyGen (p : Spec.SlhDsa.Params) (f : Shake.Fns) : Prog isa :=
  scrubAll 0 0 Clear.all (Shake.keyGen p f)

/-- `vg_slhdsa_shake_*_sign`, as emitted. -/
def sign (p : Spec.SlhDsa.Params) (f : Shake.Fns) : Prog isa :=
  scrubAll 16 32 Clear.all (Shake.sign p f)

/-- `vg_slhdsa_shake_*_verify`, as emitted. -/
def verify (p : Spec.SlhDsa.Params) (f : Shake.Fns) (g : Verify.VFns) : Prog isa :=
  scrubAll 16 32 Clear.all (Verify.verify p f g)

end VG.Impl.SlhDsa.AArch64.Fn
