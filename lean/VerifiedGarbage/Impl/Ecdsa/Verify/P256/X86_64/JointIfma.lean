module

public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64.Joint
public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Loop

/-!
# ECDSA verification over P-256 on x86-64 with AVX512_IFMA

The public joint method (`Cfg.jointVerifyWith`) with the loop over the digits
of both scalars in vectors (`Ifma.vwindow`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.X86_64
open VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64

/-- `R = [u]G + [v]Q`, the loop over the digits in vectors. -/
def ifmaPoints : Prog isa :=
  .seq (Joint.prep Ifma.publicJointIfma (p256vx.sl U) (p256vx.sl V))
    (Ifma.vwindow Ifma.publicJointIfma (jointDouble Ifma.publicJointIfma.K))

def jointVerifyP256Ifma : Prog isa := Cfg.jointVerifyWith p256vx ifmaPoints

end VG.Impl.Ecdsa.Verify.X86_64
