module

public import VerifiedGarbage.Proof.Divstep.BatchBasic
public import VerifiedGarbage.Proof.Divstep.State

/-! # The batches of the inversion with signed coefficients

`batchS` and `invRunS` (and the reduction `mredRaw` they use) without the
algebra of their proofs (`Alg.lean`, `TcS.lean`), for the proofs that only
state them (`TcSLaw.lean`).
-/

@[expose] public section

namespace VG.Proof.Divstep

/-- `t / 2^64 mod p`: `t` plus the multiple `k p` (`k = t m mod 2^64`, for
`m = -p⁻¹ mod 2^64`) that clears its low word, over `2^64`. -/
def mredRaw (p m t : Int) : Int := (t + (t * m) % 2 ^ 64 * p) / 2 ^ 64

/-- A batch of `N` divsteps, `(a, b)` by `mredRaw`. -/
def batchS (N : Nat) (p m : Int) (s : IState) : IState :=
  let t := msteps N (MSt.init s.d s.f s.g)
  ⟨t.d, (t.u * s.f + t.v * s.g) / 2 ^ N, (t.q * s.f + t.r * s.g) / 2 ^ N,
    mredRaw p m (t.u * s.a + t.v * s.b), mredRaw p m (t.q * s.a + t.r * s.b)⟩

/-- `B` such batches from the start. -/
def invRunS (N : Nat) (p m x : Int) : Nat → IState
  | 0 => ⟨1, p, x, 0, 1⟩
  | B + 1 => batchS N p m (invRunS N p m x B)

end VG.Proof.Divstep
