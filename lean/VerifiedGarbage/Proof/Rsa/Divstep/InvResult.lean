module
-- separate module: its lemmas name no ISA, so any target's batched inverse can import them; they build in parallel with PPC64LE's `IbOps` and `IbBatch`

public import VerifiedGarbage.Proof.Rsa.Divstep.InvCorrectDef
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
public import VerifiedGarbage.Proof.Divstep.Alg32
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs

/-! # The result of a batched inverse

After `3 (n + 1)` batches of 30 divsteps from `(1, p, oddInput p x)`,
`|f| = gcd(p, x)` and the corrected coefficient (`corrected`: `a`, negated if
`f < 0`, times `2^(2 B)` modulo `p`) is below `p` and `x` times it is the gcd
modulo `p` (`invRun_result`). As i686's `Proof/Rsa/X86/InvBatchRt/Body.lean`
proves for itself; independent of any ISA.
-/

@[expose] public section

namespace VG.Proof.Rsa.Divstep
open VG.Proof.Divstep

theorem corrected_range' {p : Int} (st : W32.IState) (B : Nat) (hp : 0 < p) :
    0 ≤ corrected p st B ∧ corrected p st B < p :=
  ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hp⟩

theorem corrected_cong' {p x : Int} {st : W32.IState} {B : Nat}
    (h : st.inv p x (2 ^ (2 * B))) : x * corrected p st B ≡ |st.f| [ZMOD p] := by
  have scale : corrected p st B ≡ (if st.f < 0 then -st.a else st.a) * 2 ^ (2 * B) [ZMOD p] :=
    Int.mod_modEq _ _
  have hm := scale.mul_left x
  by_cases sign : st.f < 0
  · rw [ite_eq_left sign] at hm
    have v : x * ((-st.a) * 2 ^ (2 * B)) = -(x * st.a * 2 ^ (2 * B)) := by ring
    rw [v] at hm
    rw [abs_of_neg sign]
    exact hm.trans h.1.neg.symm
  · rw [ite_eq_right sign] at hm
    rw [abs_of_nonneg (by omega)]
    exact hm.trans (by simpa only [mul_assoc] using h.1.symm)

theorem oddInput_cong' (p x : Nat) : (oddInput p x : Int) ≡ x [ZMOD (p : Int)] := by
  unfold oddInput
  split_ifs <;> simp [Int.ModEq, Nat.cast_add]

/-- After `3 (n + 1)` batches: `|f| = gcd(p, x)`, and the corrected
coefficient `y < p` with `p ∣ y x - gcd(p, x)`. -/
theorem invRun_result' {p x iv n : Nat} (odd : p % 2 = 1) (large : 1 < p)
    (inverse : (p * iv + 1) % 2 ^ 32 = 0) (pc : p < 2 ^ (32 * n)) (xc : x < 2 ^ (32 * n)) :
    let B := 3 * (n + 1)
    let st := W32.invRun 30 p iv (oddInput p x) B
    st.f.natAbs = Nat.gcd p x ∧
      (p : Int) ∣ (corrected p st B).toNat * (x : Int) - (Nat.gcd p x : Int) ∧
      (corrected p st B).toNat < p := by
  intro B st
  have done := invRun_done (inv := iv) odd pc xc
  have pi : 0 < (p : Int) := by exact_mod_cast (by omega : 0 < p)
  have nonneg := corrected_range' st B pi
  have cast : ((corrected p st B).toNat : Int) = corrected p st B := Int.toNat_of_nonneg nonneg.1
  have io : (p : Int) % 2 = 1 := by exact_mod_cast odd
  have ii : ((p : Int) * iv + 1) % 2 ^ 32 = 0 := by exact_mod_cast inverse
  have inv := W32.invRun_inv (N := 30) (x := (oddInput p x : Int)) (by decide) io (by exact_mod_cast large) ii B
  have hc := corrected_cong' (by simpa only [show 32 - 30 = 2 from rfl] using inv)
  have cx := (oddInput_cong' p x).mul_right (corrected p st B)
  have value : |st.f| = (Nat.gcd p x : Int) := by rw [← Int.natCast_natAbs, done.2]
  have result := cx.symm.trans hc
  rw [value] at result
  refine ⟨done.2, ?_, ?_⟩
  · rw [cast, mul_comm]
    exact result.symm.dvd
  · exact_mod_cast (by rw [cast]; exact nonneg.2 : ((corrected p st B).toNat : Int) < p)

/-- `a` negated modulo `p` if `f < 0`. -/
def normal (p a : Nat) (f : Int) : Nat := if f < 0 then (p - a) % p else a

/-- `a 2^k mod p`. -/
def doubled (p a k : Nat) : Nat := (a * 2 ^ k) % p

theorem doubled_zero {p a : Nat} (ha : a < p) : doubled p a 0 = a := by
  simp only [doubled, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt ha]

theorem doubled_next (p a k : Nat) : (2 * doubled p a k) % p = doubled p a (k + 1) := by
  rw [doubled, doubled, Nat.mul_mod_mod, Nat.pow_succ, Nat.mul_comm 2 (a * 2 ^ k), Nat.mul_assoc]

theorem doubled_lt {p a k : Nat} (hp : 0 < p) : doubled p a k < p := Nat.mod_lt _ hp

theorem normal_range {p a : Nat} (f : Int) (hp : 0 < p) (ha : a < p) : normal p a f < p := by
  unfold normal
  split
  · exact Nat.mod_lt _ hp
  · exact ha

theorem normal_cast {p a : Nat} (f : Int) (ha : a < p) :
    (normal p a f : Int) = (if f < 0 then -(a : Int) else (a : Int)) % p := by
  unfold normal
  split
  · rw [Int.natCast_emod, Int.ofNat_sub (by omega)]
    exact Int.neg_emod_eq_sub_emod.symm
  · exact (Int.emod_eq_of_lt (by omega) (by exact_mod_cast ha)).symm

/-- `6 (n + 1)` doublings of the normalized coefficient are the corrected one. -/
theorem correction_eq' {p a n : Nat} {st : W32.IState} (ha : a < p) (sa : st.a = (a : Int)) :
    doubled p (normal p a st.f) (6 * (n + 1)) = (corrected p st (3 * (n + 1))).toNat := by
  apply Int.ofNat_inj.mp
  rw [doubled, Int.natCast_emod, Int.natCast_mul, Int.natCast_pow, normal_cast _ ha]
  unfold corrected
  rw [sa]
  have exp : 2 * (3 * (n + 1)) = 6 * (n + 1) := by omega
  rw [exp, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  exact ((Int.mod_modEq _ _).mul_right _).eq

end VG.Proof.Rsa.Divstep
