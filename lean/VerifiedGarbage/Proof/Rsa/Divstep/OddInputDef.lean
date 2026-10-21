module
public import VerifiedGarbage.Proof.Framework.PowLit
/-! # An odd representative of the unreduced GCD input -/
@[expose] public section
namespace VG.Proof.Rsa.Divstep
def oddInput (m x : Nat) : Nat := x + if x % 2 = 0 then m else 0

end VG.Proof.Rsa.Divstep
