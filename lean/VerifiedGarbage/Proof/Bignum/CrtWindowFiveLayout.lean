module
public import VerifiedGarbage.Proof.Bignum.CrtFrame


/-! The wider window's table fits the existing public scratch contract.
The optimized path is restricted by the public modulus length. -/

@[expose] public section

namespace VG.Proof.Bignum.CrtWindowFive
open VG VG.Impl.Bignum VG.Proof.Bignum

def tabBytes32 (w : Nat) : Nat := 32 * (8 * (w + 2))

def offQ32 (w pl : Nat) : Nat := slot w 8 + slot (wsWords pl) 8 + tabBytes32 (wsWords pl)

theorem ent32_le (w : Nat) {j : Nat} (hj : j < 32) :
    slot w (8 + j) + 8 * (w + 2) ≤ slot w 8 + tabBytes32 w := by
  have h := Nat.mul_le_mul_right (8 * (w + 2)) (show 8 + j + 1 ≤ 40 by omega)
  unfold slot tabBytes32
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

/-- Even if each prime workspace is as wide as the modulus workspace,
both 32-entry tables fit within the unchanged `16 * n_len` words. -/
theorem scratch32_fits {k wp wq : Nat} (hk : 128 ≤ k)
    (hp : wp ≤ (k + 7) / 8) (hq : wq ≤ (k + 7) / 8) :
    slot ((k + 7) / 8) 8 + slot wp 8 + tabBytes32 wp + slot wq 8 + tabBytes32 wq ≤
      8 * (16 * k) := by
  unfold slot hdrBytes tabBytes32
  omega

/-- The public length guard also bounds the possibly nonstandard prime widths. -/
theorem prime_scratch32_fits {k pl ql : Nat} (hk : 128 ≤ k)
    (hp : pl < k) (hq : ql < k) :
    offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤
      8 * (16 * k) := by
  apply scratch32_fits hk
  · unfold wsWords; omega
  · unfold wsWords; omega

end VG.Proof.Bignum.CrtWindowFive
