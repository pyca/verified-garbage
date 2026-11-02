module

public import VerifiedGarbage.Proof.Divstep.Red30Def
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef

/-! # The inverse from batches of 30 divsteps

`inv30 n a m`: after the `3 (n + 1)` batches that finish for `a, m < 2^(32 n)`,
the coefficient `d` of `f` with `f`'s sign, modulo `m` (`Inv30.lean`: `x < m`
with `x a ≡ gcd(a, m) (mod m)` for odd `m > 1`). -/

@[expose] public section

namespace VG.Proof.Rsa.Divstep
open VG.Proof.Divstep

def inv30 (n a m : Nat) : Nat :=
  ((if (W32.invRun 30 m 0 (oddInput m a) (3 * (n + 1))).f < 0
      then -((W32.deRun m (oddInput m a) (3 * (n + 1))).1 : Int)
      else (W32.deRun m (oddInput m a) (3 * (n + 1))).1) % (m : Int)).toNat

end VG.Proof.Rsa.Divstep
