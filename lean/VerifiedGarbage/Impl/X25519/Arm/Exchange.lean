module

public import VerifiedGarbage.Impl.X25519.Arm.Words
public import VerifiedGarbage.Impl.Xdh.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# X25519 exchange on ARMv7, as emitted

`vg_x25519_exchange` and `vg_x25519_exchange_umaal` are `Impl.Xdh.Arm.exchange` calling
`vg_x25519` or `vg_x25519_umaal`, with their cleanup: the 8 bytes of stack their frames use
zeroed, then the registers a callee may change, but the result's 32 bits, and the flags set
to constants.
-/

@[expose] public section

namespace VG.Impl.X25519.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_x25519_exchange`: the check of `vg_x25519`'s result, then its cleanup. -/
def exchange : Prog isa := scrubAll 32 8 (Impl.Xdh.Arm.exchange "vg_x25519" Impl.X25519.Arm.x25519 32)

/-- `vg_x25519_exchange_umaal`, as `exchange` with `vg_x25519_umaal`. -/
def exchangeUmaal : Prog isa :=
  scrubAll 32 8 (Impl.Xdh.Arm.exchange "vg_x25519_umaal" Impl.X25519.Arm.Words.x25519Umaal 32)

end VG.Impl.X25519.Arm.Fn
