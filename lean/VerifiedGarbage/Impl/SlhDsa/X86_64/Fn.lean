module

public import VerifiedGarbage.Impl.SlhDsa.X86_64.Shake
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Verify
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # SLH-DSA (SHAKE) on x86-64: the functions as emitted

`vg_slhdsa_shake_*_keygen` of the parameter set `p` over the functions `f`
it calls, then its cleanup (`Impl.Scrub.X86_64.scrubAll v 0 48`): every
vector register at the level `v` and every caller-saved register cleared,
and the 48 bytes below the stack pointer, which its calls use, wiped;
`vg_slhdsa_shake_*_sign` likewise, with the 120 bytes below the stack pointer
(its frame of 72 bytes and its calls') wiped, and `vg_slhdsa_shake_*_verify`
with the 112 bytes below the stack pointer wiped.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `vg_slhdsa_shake_*_keygen`, as emitted. -/
def keyGen (v : VecLevel) (p : Spec.SlhDsa.Params) (f : Shake.Fns) : Prog isa :=
  scrubAll v 0 48 (Shake.keyGen p f)

/-- `vg_slhdsa_shake_*_sign`, as emitted. -/
def sign (v : VecLevel) (p : Spec.SlhDsa.Params) (f : Shake.Fns) : Prog isa :=
  scrubAll v 32 120 (Shake.sign p f)

/-- `vg_slhdsa_shake_*_verify`, as emitted. -/
def verify (v : VecLevel) (p : Spec.SlhDsa.Params) (f : Shake.Fns) (g : Verify.VFns) : Prog isa :=
  scrubAll v 32 112 (Verify.verify p f g)

end VG.Impl.SlhDsa.X86_64.Fn
