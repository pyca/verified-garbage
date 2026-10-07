import VerifiedGarbage.Proof.Divstep.BatchBasic

/-! # The state and transitions of 32-bit batched inversion -/
namespace VG.Proof.Divstep.W32

/-- `t / 2^32 mod p`: `t` plus the multiple `k p` (`k = t m mod 2^32`, for
`m = -p⁻¹ mod 2^32`) that clears its low word, over `2^32`. -/
def mredRaw (p m t : Int) : Int := (t + (t * m) % 2 ^ 32 * p) / 2 ^ 32

/-- Into `[0, p)` from `(-p, 2p)`. -/
def norm (p t : Int) : Int := if t < 0 then t + p else if p ≤ t then t - p else t

def mred (p m t : Int) : Int := norm p (mredRaw p m t)

/-- The state of the inversion. -/
structure IState where
  d : Int
  f : Int
  g : Int
  a : Int
  b : Int

/-- A batch of `N` divsteps. -/
def batch (N : Nat) (p m : Int) (s : IState) : IState :=
  let t := msteps N (MSt.init s.d s.f s.g)
  ⟨t.d, (t.u * s.f + t.v * s.g) / 2 ^ N, (t.q * s.f + t.r * s.g) / 2 ^ N,
    mred p m (t.u * s.a + t.v * s.b), mred p m (t.q * s.a + t.r * s.b)⟩

/-- `B` batches from the start. -/
def invRun (N : Nat) (p m x : Int) : Nat → IState
  | 0 => ⟨1, p, x, 0, 1⟩
  | B + 1 => batch N p m (invRun N p m x B)

theorem batch_d (N : Nat) (p m : Int) (s : IState) :
    (batch N p m s).d = (msteps N (MSt.init s.d s.f s.g)).d := rfl

theorem batch_a (N : Nat) (p m : Int) (s : IState) :
    (batch N p m s).a =
      mred p m ((msteps N (MSt.init s.d s.f s.g)).u * s.a +
        (msteps N (MSt.init s.d s.f s.g)).v * s.b) := rfl

theorem batch_b (N : Nat) (p m : Int) (s : IState) :
    (batch N p m s).b =
      mred p m ((msteps N (MSt.init s.d s.f s.g)).q * s.a +
        (msteps N (MSt.init s.d s.f s.g)).r * s.b) := rfl

end VG.Proof.Divstep.W32
