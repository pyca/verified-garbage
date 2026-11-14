module

public import VerifiedGarbage.Proof.Divstep.BatchS
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
public import Mathlib.Algebra.Order.Ring.Abs

/-! # The algebra of the signed batches, as a class (`TcSLaw`)

What a target's batched inverse over 64-bit words uses of `TcS.lean`,
`TcSBounds.lean` and `Tc.lean`, stated without their algebra
(`Alg.lean`): a proof takes `[TcSLaw]`, and the registrations take the
instance from `TcSBounds.lean`, so that only they import that algebra.
-/

@[expose] public section

namespace VG.Proof.Divstep

class TcSLaw : Prop where
  comb_le2 {N : Nat} (hN : N ≤ 62) {y z a b p : Int} (hp : 0 < p) (hyz : |y| + |z| ≤ 2 ^ N)
    (ha : |a| ≤ 2 * p) (hb : |b| ≤ 2 * p) : |y * a + z * b| ≤ 2 ^ 63 * p
  mredRaw_nat {A B H p m W k E R : Nat} {t : Int} (hB : B = 2 ^ 64) (hH : H = 2 ^ 63) (hA : 0 < A)
    (hp : 0 < p) (hpA : p < A) (hm : (p * m + 1) % B = 0) (ht : |t| ≤ 2 ^ 63 * p)
    (hW1 : W < A * B) (hWt : (W : Int) % ((A * B : Nat) : Int) = t % ((A * B : Nat) : Int))
    (hk : k = W % B * m % B)
    (hE : E = (W + A * B * (if A * H ≤ W then B - 1 else 0) + k * p) % (A * B * B))
    (hR : R = E / B) :
    (R : Int) % ((A * B : Nat) : Int) = mredRaw p m t % ((A * B : Nat) : Int)
  invRunS_bounds {N : Nat} (hN : N ≤ 62) {p m x M : Int} (hp : p % 2 = 1) (hp0 : 0 < p)
    (hm : (p * m + 1) % 2 ^ 64 = 0) (hx0 : 0 ≤ x) (hpM : p ≤ M) (hxM : x ≤ M) (B : Nat) :
    |(invRunS N p m x B).d| ≤ 1 + 2 * (N * B : Nat) ∧ (invRunS N p m x B).f % 2 = 1 ∧
      |(invRunS N p m x B).f| ≤ M ∧ |(invRunS N p m x B).g| ≤ M ∧
      -p < (invRunS N p m x B).a ∧ (invRunS N p m x B).a < 2 * p ∧
      -p < (invRunS N p m x B).b ∧ (invRunS N p m x B).b < 2 * p
  invRunS_done {N B : Nat} (hN : N ≤ 62) {p m u : Nat} (hp : p % 2 = 1)
    (hm : ((p : Int) * m + 1) % 2 ^ 64 = 0)
    (hdone : (divsteps (N * B) (1, (p : Int), (Rsa.Divstep.oddInput p u : Int))).2.2 = 0 ∧
      (divsteps (N * B) (1, (p : Int), (Rsa.Divstep.oddInput p u : Int))).2.1.natAbs = Nat.gcd p u) :
    (invRunS N p m (Rsa.Divstep.oddInput p u) B).g = 0 ∧
      (invRunS N p m (Rsa.Divstep.oddInput p u) B).f.natAbs = Nat.gcd p u ∧
      (u : Int) * ((if 0 ≤ (invRunS N p m (Rsa.Divstep.oddInput p u) B).f then 1 else -1) *
        (invRunS N p m (Rsa.Divstep.oddInput p u) B).a) * 2 ^ ((64 - N) * B) ≡
        (Nat.gcd p u : Int) [ZMOD p]
  comb_le {u v f g p : Int} (huv : |u| + |v| ≤ 2 ^ 59) (hf : |f| ≤ p) (hg : |g| ≤ p) :
    |u * f + v * g| ≤ 2 ^ 59 * p
  shr_nat {H V D c B : Nat} {y z : Int} (hc : 2 ^ 59 = c) (hB : 2 ^ 64 = B) (hH : 0 < H) (hV1 : V < 2 * H)
    (hVy : (V : Int) % ((2 * H : Nat) : Int) = y % ((2 * H : Nat) : Int)) (hy1 : -(H : Int) ≤ y) (hy2 : y < H)
    (hz : y = 2 ^ 59 * z) (hD : D = (V + 2 * H * (if H ≤ V then B - 1 else 0)) / c % (2 * H)) :
    (D : Int) % ((2 * H : Nat) : Int) = z % ((2 * H : Nat) : Int)

end VG.Proof.Divstep
