module
import VerifiedGarbage.Proof.Framework.PowLit


/-! Positional arithmetic for rows of rectangular multiplication tiles. -/

@[expose] public section

namespace VG.Proof.Bignum.Rectangular

theorem extend_carry {L P C T I O R D A : Nat}
    (prev : L+P*C=T+I) (step : O+R*D=A+C) :
    L+P*O+(P*R)*D=T+P*A+I := by
  grind

end VG.Proof.Bignum.Rectangular
