module

public import VerifiedGarbage.Proof.Divstep.Red30Def
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Red30
import VerifiedGarbage.Proof.Divstep.Alg32
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.Order.Ring.Abs

/-! # The coefficients' update of libsecp256k1's `update_de`, for any batch of `N` divsteps

A batch's row `(u, v)` takes the coefficients `(d, e)` to `(u d + v e + md p) / 2^N`, with `md`
the multiple of `p` that clears the sum's low `N` bits (`mdOf`, from `np = -p⁻¹ mod 2^N`), and
`u` (`v`) added to it where `d` (`e`) is negative, as if `d + p` (`e + p`) took its place. So the
result is the sum divided by `2^N` modulo `p` exactly (`deUpd_dvd`, `deUpd_cong`), and stays in
`(-2p, p)` from inputs there (`deUpd_range`), with no reduction. For batches of 30 the pairs are
those of `Red30Def`'s `deRun` modulo `p` (`deRunL_cong`).
-/

@[expose] public section

namespace VG.Proof.Divstep

/-- The multiple of `p` for the row `(u, v)` and the inputs `d`, `e`. -/
def mdOf (N : Nat) (np u v d e : Int) : Int :=
  let md0 := (if d < 0 then u else 0) + (if e < 0 then v else 0)
  md0 - (md0 - np * (u * d + v * e)) % 2 ^ N

/-- The row `(u, v)` of a batch on the inputs `d`, `e`. -/
def deUpd (N : Nat) (p np u v d e : Int) : Int := (u * d + v * e + mdOf N np u v d e * p) / 2 ^ N

theorem mdOf_dvd {N : Nat} {p np u v d e : Int} (hnp : (p * np + 1) % 2 ^ N = 0) :
    (2 : Int) ^ N ∣ u * d + v * e + mdOf N np u v d e * p := by
  unfold mdOf
  simp only
  generalize hm : (if d < 0 then u else 0) + (if e < 0 then v else 0) = md0
  generalize hs : u * d + v * e = S
  have h1 : (2 : Int) ^ N ∣ p * np + 1 := Int.dvd_of_emod_eq_zero hnp
  have h2 : (2 : Int) ^ N ∣ (md0 - np * S) - (md0 - np * S) % 2 ^ N := Int.dvd_self_sub_of_emod_eq rfl
  have e : S + (md0 - (md0 - np * S) % 2 ^ N) * p =
      ((md0 - np * S) - (md0 - np * S) % 2 ^ N) * p + (p * np + 1) * S := by ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left h1 _)

theorem mdOf_range {N : Nat} {np u v d e : Int} :
    (if d < 0 then u else 0) + (if e < 0 then v else 0) - 2 ^ N < mdOf N np u v d e ∧
      mdOf N np u v d e ≤ (if d < 0 then u else 0) + (if e < 0 then v else 0) := by
  unfold mdOf
  simp only
  have h0 : (0 : Int) < 2 ^ N := pow_pos (by decide) N
  have a := Int.emod_nonneg ((if d < 0 then u else 0) + (if e < 0 then v else 0) - np * (u * d + v * e)) h0.ne'
  have b := Int.emod_lt_of_pos ((if d < 0 then u else 0) + (if e < 0 then v else 0) - np * (u * d + v * e)) h0
  omega

/-- `|md| < 2^(N + 1)` for a row of a batch of `N`. -/
theorem mdOf_abs {N : Nat} {np u v d e : Int} (huv : |u| + |v| ≤ 2 ^ N) :
    -2 ^ (N + 1) < mdOf N np u v d e ∧ mdOf N np u v d e ≤ 2 ^ N := by
  obtain ⟨a, b⟩ := mdOf_range (N := N) (np := np) (u := u) (v := v) (d := d) (e := e)
  have hu := abs_le.mp (show |u| ≤ 2 ^ N by have := abs_nonneg v; linarith)
  have hv := abs_le.mp (show |v| ≤ 2 ^ N by have := abs_nonneg u; linarith)
  have hp : (2 : Int) ^ (N + 1) = 2 * 2 ^ N := by ring
  rw [hp]
  have hu' := le_abs_self u; have hv' := le_abs_self v
  have hu'' := neg_abs_le u; have hv'' := neg_abs_le v
  constructor
  · have : -(|u| + |v|) ≤ (if d < 0 then u else 0) + (if e < 0 then v else 0) := by
      split <;> split <;> linarith [abs_nonneg u, abs_nonneg v]
    linarith
  · have : (if d < 0 then u else 0) + (if e < 0 then v else 0) ≤ |u| + |v| := by
      split <;> split <;> linarith [abs_nonneg u, abs_nonneg v]
    linarith

theorem deUpd_mul {N : Nat} {p np u v d e : Int} (hnp : (p * np + 1) % 2 ^ N = 0) :
    2 ^ N * deUpd N p np u v d e = u * d + v * e + mdOf N np u v d e * p := by
  unfold deUpd
  exact Int.mul_ediv_cancel' (mdOf_dvd hnp)

theorem deUpd_cong {N : Nat} {p np u v d e : Int} (hnp : (p * np + 1) % 2 ^ N = 0) :
    2 ^ N * deUpd N p np u v d e ≡ u * d + v * e [ZMOD p] := by
  rw [deUpd_mul hnp]
  exact (Int.modEq_iff_dvd.mpr ⟨-mdOf N np u v d e, by ring⟩)

/-- From inputs in `(-2p, p)`, the result is in `(-2p, p)`. -/
theorem deUpd_range {N : Nat} {p np u v d e : Int} (hnp : (p * np + 1) % 2 ^ N = 0) (hp : 0 < p)
    (huv : |u| + |v| ≤ 2 ^ N) (hd : -2 * p < d ∧ d < p) (he : -2 * p < e ∧ e < p) :
    -2 * p < deUpd N p np u v d e ∧ deUpd N p np u v d e < p := by
  have h0 : (0 : Int) < 2 ^ N := pow_pos (by decide) N
  have hm := deUpd_mul (u := u) (v := v) (d := d) (e := e) hnp
  obtain ⟨r1, r2⟩ := mdOf_range (N := N) (np := np) (u := u) (v := v) (d := d) (e := e)
  -- `d + p [d < 0]` and `e + p [e < 0]` are in `(-p, p)`.
  set dd := d + (if d < 0 then p else 0) with hdd
  set ee := e + (if e < 0 then p else 0) with hee
  have bd : -p < dd ∧ dd < p := by rw [hdd]; split <;> constructor <;> linarith [hd.1, hd.2]
  have be : -p < ee ∧ ee < p := by rw [hee]; split <;> constructor <;> linarith [he.1, he.2]
  set t := (if d < 0 then u else 0) + (if e < 0 then v else 0) - mdOf N np u v d e with ht
  have t0 : 0 ≤ t := by linarith
  have t1 : t < 2 ^ N := by linarith
  have es : u * d + v * e + mdOf N np u v d e * p = u * dd + v * ee - t * p := by
    rw [hdd, hee, ht]; split <;> split <;> ring
  -- `|u dd + v ee| ≤ 2^N (p - 1)`.
  have hb : |u * dd + v * ee| ≤ (|u| + |v|) * (p - 1) := by
    have a1 : |u * dd| ≤ |u| * (p - 1) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg u)
    have a2 : |v * ee| ≤ |v| * (p - 1) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg v)
    calc |u * dd + v * ee| ≤ |u * dd| + |v * ee| := abs_add_le _ _
      _ ≤ |u| * (p - 1) + |v| * (p - 1) := add_le_add a1 a2
      _ = (|u| + |v|) * (p - 1) := by ring
  have hb2 : (|u| + |v|) * (p - 1) ≤ 2 ^ N * (p - 1) := mul_le_mul_of_nonneg_right huv (by linarith)
  have hl := (abs_le.mp (hb.trans hb2)).1
  have hr := (abs_le.mp (hb.trans hb2)).2
  have tp : t * p < 2 ^ N * p := mul_lt_mul_of_pos_right t1 hp
  have tp0 : 0 ≤ t * p := mul_nonneg t0 hp.le
  rw [es] at hm
  constructor
  · by_contra hc
    have : 2 ^ N * deUpd N p np u v d e ≤ 2 ^ N * (-2 * p) := mul_le_mul_of_nonneg_left (not_lt.mp hc) h0.le
    nlinarith
  · by_contra hc
    have : 2 ^ N * p ≤ 2 ^ N * deUpd N p np u v d e := mul_le_mul_of_nonneg_left (not_lt.mp hc) h0.le
    nlinarith

/-- The coefficients over a run of batches of 30, from `(0, 1)`, with `np = -p⁻¹ mod 2^30`. -/
def deRunL (p np x : Nat) : Nat → Int × Int
  | 0 => (0, 1)
  | i + 1 =>
    let s := W32.invRun 30 p 0 x i
    let t := msteps 30 (MSt.init s.d s.f s.g)
    (deUpd 30 p np t.u t.v (deRunL p np x i).1 (deRunL p np x i).2,
      deUpd 30 p np t.q t.r (deRunL p np x i).1 (deRunL p np x i).2)

/-- They are `deRun`'s modulo `p`, and stay in `(-2p, p)`. -/
theorem deRunL_cong {p np x : Nat} (hp : p % 2 = 1) (hp1 : 1 < p) (hnp : ((p : Int) * np + 1) % 2 ^ 30 = 0) :
    ∀ i, (deRunL p np x i).1 ≡ (W32.deRun p x i).1 [ZMOD p] ∧ (deRunL p np x i).2 ≡ (W32.deRun p x i).2 [ZMOD p] ∧
      (-2 * (p : Int) < (deRunL p np x i).1 ∧ (deRunL p np x i).1 < p) ∧
      (-2 * (p : Int) < (deRunL p np x i).2 ∧ (deRunL p np x i).2 < p)
  | 0 => by
    have : (1 : Int) < p := by exact_mod_cast hp1
    simp only [deRunL, W32.deRun]
    refine ⟨Int.ModEq.refl _, by simp [Int.ModEq], ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  | i + 1 => by
    obtain ⟨c1, c2, r1, r2⟩ := deRunL_cong hp hp1 hnp i
    have hp0 : (0 : Int) < p := by omega
    have bnd := msteps_bnd (W32.invRun 30 p 0 x i).d (W32.invRun 30 p 0 x i).f (W32.invRun 30 p 0 x i).g 30
    simp only [deRunL, W32.deRun, W32.deStep]
    obtain ⟨a1, a2⟩ := W32.red30_spec hp ((msteps 30 (MSt.init (W32.invRun 30 p 0 x i).d (W32.invRun 30 p 0 x i).f
      (W32.invRun 30 p 0 x i).g)).u * (W32.deRun p x i).1 + (msteps 30 (MSt.init (W32.invRun 30 p 0 x i).d
      (W32.invRun 30 p 0 x i).f (W32.invRun 30 p 0 x i).g)).v * (W32.deRun p x i).2)
    obtain ⟨b1, b2⟩ := W32.red30_spec hp ((msteps 30 (MSt.init (W32.invRun 30 p 0 x i).d (W32.invRun 30 p 0 x i).f
      (W32.invRun 30 p 0 x i).g)).q * (W32.deRun p x i).1 + (msteps 30 (MSt.init (W32.invRun 30 p 0 x i).d
      (W32.invRun 30 p 0 x i).f (W32.invRun 30 p 0 x i).g)).r * (W32.deRun p x i).2)
    have hpI : (p : Int) % 2 = 1 := by exact_mod_cast hp
    refine ⟨?_, ?_, deUpd_range hnp hp0 bnd.1 r1 r2, deUpd_range hnp hp0 bnd.2 r1 r2⟩
    · refine W32.cancel_pow2 (N := 30) hpI hp0 ((deUpd_cong hnp).trans ?_)
      exact ((c1.mul_left _).add (c2.mul_left _)).trans a2.symm
    · refine W32.cancel_pow2 (N := 30) hpI hp0 ((deUpd_cong hnp).trans ?_)
      exact ((c1.mul_left _).add (c2.mul_left _)).trans b2.symm

end VG.Proof.Divstep
