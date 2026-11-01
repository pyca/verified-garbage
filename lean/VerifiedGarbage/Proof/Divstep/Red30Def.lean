module

public import VerifiedGarbage.Proof.Divstep.Alg32Def

/-! # Batches of 30 divsteps: the coefficients as functions of the inputs

`red30 p t` is `t / 2^30` modulo the odd `p`, as `t ((p + 1) / 2)^30 mod p`.
`deRun p x i` is the pair `(d, e)` after `i` batches from `(0, 1)`, each batch
replacing it by `(u d + v e, q d + r e) / 2^30` modulo `p` (`Red30.lean`). -/

@[expose] public section

namespace VG.Proof.Divstep.W32

def red30 (p : Nat) (t : Int) : Nat := (t * (((p + 1) / 2 : Nat) : Int) ^ 30 % (p : Int)).toNat

/-- The coefficients after a batch from `s`. -/
def deStep (p : Nat) (s : IState) (de : Nat × Nat) : Nat × Nat :=
  (red30 p ((msteps 30 (MSt.init s.d s.f s.g)).u * de.1 + (msteps 30 (MSt.init s.d s.f s.g)).v * de.2),
    red30 p ((msteps 30 (MSt.init s.d s.f s.g)).q * de.1 + (msteps 30 (MSt.init s.d s.f s.g)).r * de.2))

/-- The coefficients after `i` batches for `p` and the odd input `x`. -/
def deRun (p x : Nat) : Nat → Nat × Nat
  | 0 => (0, 1)
  | i + 1 => deStep p (invRun 30 p 0 x i) (deRun p x i)

end VG.Proof.Divstep.W32
