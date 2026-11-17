module

import VerifiedGarbage.Proof.Ed25519.Scalar
public import VerifiedGarbage.Impl.Ed25519.Arm.Scalar
public import VerifiedGarbage.Proof.Ed25519.Arm.Field
public import VerifiedGarbage.Proof.X25519.Arm.Pass
import VerifiedGarbage.Proof.Framework.Offset

/-! Merged from `Proof.Ed25519.Arm.ScalarNat`. -/

@[expose] public section

section
/-! Radix-65536 arithmetic for subgroup-order reduction. -/
namespace VG.Proof.Ed25519.Arm
open VG.Proof.X25519.Arm VG.Spec.Ed25519 VG.Impl.Ed25519.Arm

theorem scalarComplement_lt (k : Nat) : scalarComplement k < 65536 := by
  unfold scalarComplement; omega_using []

theorem scalarComplement_val : val16 scalarComplement 16 + L + 1 = 2 ^ 256 := by decide

theorem scalarSubtract_facts {f : Nat → Nat} (hf : val16 f 16 < 2 * L) :
    chain (fun k => f k + scalarComplement k) 1 16 ≤ 1 ∧
    val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
      (f k) (out (fun j => f j + scalarComplement j) 1 k)) 16 = val16 f 16 % L := by
  have hv := chain_val (fun k => f k + scalarComplement k) 1 16
  rw [val16_add] at hv
  have hc := scalarComplement_val
  have hL := order_pos
  have hB := order_bound
  have hout := val16_lt (f := out (fun k => f k + scalarComplement k) 1) (n := 16)
    fun _ _ => out_lt _ _ _
  have hcarry : chain (fun k => f k + scalarComplement k) 1 16 ≤ 1 := by
    have : 2 ^ 256 * chain (fun k => f k + scalarComplement k) 1 16 < 2 ^ 256 * 2 := by omega_using [hf, hv, hc]
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left this)
  refine ⟨hcarry, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcarry with hz | ho
  · have he : val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
        (f k) (out (fun j => f j + scalarComplement j) 1 k)) 16 = val16 f 16 :=
      val16_congr fun _ _ => by rw [hz]; rfl
    rw [he, Nat.mod_eq_of_lt (by rw [hz] at hv; omega_using [hv, hc, hout])]
  · have he : val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
        (f k) (out (fun j => f j + scalarComplement j) 1 k)) 16 =
        val16 (out (fun j => f j + scalarComplement j) 1) 16 :=
      val16_congr fun _ _ => by rw [ho]; rfl
    rw [he]
    have heq : val16 f 16 = val16 (out (fun j => f j + scalarComplement j) 1) 16 + L := by
      rw [ho] at hv; omega_using [hv, hc]
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [hf, hv, hc, ho])]

theorem scalarCompare_carry {f : Nat → Nat} (hf : val16 f 16 < 2 ^ 256) :
    chain (fun k => f k + scalarComplement k) 1 16 = if val16 f 16 < L then 0 else 1 := by
  have hv := chain_val (fun k => f k + scalarComplement k) 1 16
  rw [val16_add] at hv
  have hc := scalarComplement_val
  have hl := order_pos
  have hout := val16_lt (f := out (fun k => f k + scalarComplement k) 1) (n := 16)
    fun _ _ => out_lt _ _ _
  split <;> omega_arith

/-! The constants of the reduction a product at a time: `d = 16 L - 2²⁵⁶`,
`c = L - 2²⁵²` and `L - 64 c`. -/

theorem scalarD_eq : 16 * L - 2 ^ 256 = 443877084437957656573631004654138375888 := by decide
theorem scalarD_val : val16 scalarD 16 = 16 * L - 2 ^ 256 := by decide
theorem scalarD_val9 : val16 scalarD 9 = 16 * L - 2 ^ 256 := by decide
theorem scalarD_lt (j : Nat) : scalarD j < 65536 := Nat.mod_lt _ (by decide)
theorem scalarD_high : ∀ j < 16, 9 ≤ j → scalarD j = 0 := by decide
theorem scalarC_val : val16 scalarC 16 = L - 2 ^ 252 := by decide
theorem scalarC_lt (j : Nat) : scalarC j < 65536 := Nat.mod_lt _ (by decide)
theorem scalarC_high : ∀ j < 16, 8 ≤ j → scalarC j = 0 := by decide
theorem scalarE_val : val16 scalarE 16 = 64 * 2 ^ 252 - 63 * L := by decide
theorem scalarE_lt (j : Nat) : scalarE j < 65536 := Nat.mod_lt _ (by decide)
theorem val16_ones : val16 (fun _ => 65535) 16 + 1 = 2 ^ 256 := by decide

/-- The top of the second product by `d` is at most 1, and `T` is below
`2²⁵⁸` and congruent to `N`. -/
theorem scalarSum_facts {N0 N1 P1lo P1hi P2lo h : Nat} (hN0 : N0 < 2 ^ 256) (hN1 : N1 < 2 ^ 256)
    (hP2 : P2lo < 2 ^ 256) (h1 : P1lo + 2 ^ 256 * P1hi = N1 * (16 * L - 2 ^ 256))
    (h2 : P2lo + 2 ^ 256 * h = P1hi * (16 * L - 2 ^ 256)) :
    h ≤ 1 ∧ ∀ T, T + P1lo = N0 + 2 ^ 256 + P2lo + (1 - h) * (16 * L - 2 ^ 256) →
      T < 2 ^ 258 ∧ T % L = (N0 + 2 ^ 256 * N1) % L := by
  rw [scalarD_eq] at h1 h2 ⊢
  obtain hh1 : h ≤ 1 := by omega_using [h1, h2, hN1]
  refine ⟨hh1, fun T hT => ⟨by omega_using [hT, hN0, hP2, hh1], ?_⟩⟩
  obtain e : T + L * (16 * (N1 + h)) = N0 + 2 ^ 256 * N1 + L * (16 * (1 + P1hi)) := by
    simp only [L]
    omega_using [h1, h2, hT, hh1]
  rw [← Nat.add_mul_mod_self_left T L (16 * (N1 + h)), e, Nat.add_mul_mod_self_left]

/-- `U = l + (64 - q) c + (L - 64 c)` is below `2 L` and congruent to
`l + 2²⁵² q`. -/
theorem scalarLow_facts {l q : Nat} (hl : l < 2 ^ 252) (hq : q ≤ 64) :
    l + (64 - q) * (L - 2 ^ 252) + (64 * 2 ^ 252 - 63 * L) < 2 * L ∧
    (l + (64 - q) * (L - 2 ^ 252) + (64 * 2 ^ 252 - 63 * L)) % L = (l + 2 ^ 252 * q) % L := by
  refine ⟨by simp only [L]; omega_using [hl, hq], ?_⟩
  obtain e : l + (64 - q) * (L - 2 ^ 252) + (64 * 2 ^ 252 - 63 * L) + L * q =
      l + 2 ^ 252 * q + L * 1 := by
    simp only [L]
    omega_using [hl, hq]
  rw [← Nat.add_mul_mod_self_left _ L q, e, Nat.add_mul_mod_self_left]

/-- The sums of `T`'s limbs, for `g = 1 - h`. -/
def scalarSumC (n p1 p2 : Nat → Nat) (g k : Nat) : Nat :=
  n k + 65535 - p1 k + p2 k + g * scalarD k

theorem scalarSumC_le {n p1 p2 : Nat → Nat} {g : Nat} (hn : ∀ k < 16, n k < 65536)
    (hp2 : ∀ k < 16, p2 k < 65536) (hg : g ≤ 1) :
    ∀ k < 16, scalarSumC n p1 p2 g k + 65536 ≤ 2 ^ 32 := by
  intro k hk
  have := hn k hk; have := hp2 k hk; have := scalarD_lt k
  have : g * scalarD k ≤ 1 * scalarD k := Nat.mul_le_mul_right _ hg
  simp only [scalarSumC]
  omega_arith

theorem scalarSumC_val {n p1 p2 : Nat → Nat} {g : Nat} (hp1 : ∀ k < 16, p1 k < 65536) :
    val16 (scalarSumC n p1 p2 g) 16 + val16 p1 16 + 1 =
      val16 n 16 + 2 ^ 256 + val16 p2 16 + g * (16 * L - 2 ^ 256) := by
  obtain e : val16 (fun k => scalarSumC n p1 p2 g k + p1 k) 16 =
      val16 (fun k => (fun k => (fun k => n k + (fun _ => 65535) k) k + p2 k) k +
        (fun k => g * scalarD k) k) 16 :=
    val16_congr fun k hk => by have := hp1 k hk; simp only [scalarSumC]; omega_arith
  rw [val16_add (scalarSumC n p1 p2 g) p1, val16_add _ (fun k => g * scalarD k),
    val16_add _ p2, val16_add n (fun _ => 65535), val16_cmul, scalarD_val] at e
  have := val16_ones
  omega_arith

/-- The sums of `U`'s limbs, for `g = 64 - q`. -/
def scalarLowC (l : Nat → Nat) (g k : Nat) : Nat := l k + g * scalarC k + scalarE k

theorem scalarLowC_le {l : Nat → Nat} {g : Nat} (hl : ∀ k < 16, l k < 65536) (hg : g ≤ 64) :
    ∀ k < 16, scalarLowC l g k + 65536 ≤ 2 ^ 32 := by
  intro k hk
  have := hl k hk; have := scalarC_lt k; have := scalarE_lt k
  have : g * scalarC k ≤ 64 * 65535 := Nat.mul_le_mul hg (by omega_arith)
  simp only [scalarLowC]
  omega_arith

theorem scalarLowC_val (l : Nat → Nat) (g : Nat) :
    val16 (scalarLowC l g) 16 = val16 l 16 + g * (L - 2 ^ 252) + (64 * 2 ^ 252 - 63 * L) := by
  rw [← scalarC_val, ← scalarE_val, ← val16_cmul, ← val16_add, ← val16_add]
  rfl

/-- Limb 15 cut to 12 bits: the number modulo `2²⁵²`. -/
def mask12 (l : Nat → Nat) (k : Nat) : Nat := if k = 15 then l 15 % 4096 else l k

theorem mask12_facts {l : Nat → Nat} (hl : ∀ k < 16, l k < 65536) :
    val16 l 16 = val16 (mask12 l) 16 + 2 ^ 252 * (l 15 / 4096) ∧ val16 (mask12 l) 16 < 2 ^ 252 ∧
      (∀ k < 16, mask12 l k < 65536) := by
  have e : val16 (mask12 l) 15 = val16 l 15 :=
    val16_congr fun k hk => by simp only [mask12, show k ≠ 15 by omega_arith, ite_false]
  have h15 := hl 15 (by decide)
  have hlo := val16_lt (f := l) (n := 15) fun k hk => hl k (by omega_arith)
  rw [show 16 * 15 = 240 from rfl] at hlo
  have hm : l 15 = l 15 % 4096 + 4096 * (l 15 / 4096) := (Nat.mod_add_div _ _).symm
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · rw [val16_succ l 15, val16_succ (mask12 l) 15, e, show mask12 l 15 = l 15 % 4096 from rfl,
      show 16 * 15 = 240 from rfl]
    conv => lhs; rw [hm]
    rw [Nat.mul_add, show (2 : Nat) ^ 252 = 2 ^ 240 * 4096 from rfl, Nat.mul_assoc]; omega_arith
  · rw [val16_succ (mask12 l) 15, e, show mask12 l 15 = l 15 % 4096 from rfl, show 16 * 15 = 240 from rfl]
    have : 2 ^ 240 * (l 15 % 4096) ≤ 2 ^ 240 * 4095 :=
      Nat.mul_le_mul_left _ (by have := Nat.mod_lt (l 15) (show 4096 > 0 by decide); omega_arith)
    rw [show (2 : Nat) ^ 252 = 2 ^ 240 * 4096 from rfl]; omega_arith
  · simp only [mask12]; split
    · exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    · exact hl k hk

/-- A number of limbs that is at most 1 is its limb 0. -/
theorem val16_low1 {f : Nat → Nat} {n : Nat} (h : val16 f (1 + n) ≤ 1) : val16 f (1 + n) = f 0 := by
  have e := val16_append f 1 n
  rw [show 16 * 1 = 16 from rfl] at e
  have e1 : val16 f 1 = f 0 := by simp only [val16, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  generalize val16 (fun k => f (1 + k)) n = r at e
  omega_arith

/-! A row of a product by a number of `w` limbs, as the field's
(`Proof/X25519/Arm/Limbs.lean`) for 16. -/

/-- The limbs after row `i`: those below `i`, the row's limbs, and its carry. -/
def rowAccW (w : Nat) (acc a b : Nat → Nat) (i k : Nat) : Nat :=
  if k < i then acc k else if k < i + w then out (rowC acc a b i) 0 (k - i)
  else chain (rowC acc a b i) 0 w

theorem rowW_val {w : Nat} {acc a b : Nat → Nat} {i : Nat}
    (hv : val16 acc (i + w) = val16 a i * val16 b w) :
    val16 (rowAccW w acc a b i) (i + (w + 1)) = val16 a (i + 1) * val16 b w := by
  have e1 : val16 (rowAccW w acc a b i) i = val16 acc i :=
    val16_congr fun k hk => by simp only [rowAccW, hk, ite_true]
  have e2 : val16 (fun k => rowAccW w acc a b i (i + k)) (w + 1) =
      val16 (out (rowC acc a b i) 0) w + 2 ^ (16 * w) * chain (rowC acc a b i) 0 w := by
    rw [val16_succ, val16_congr (g := out (rowC acc a b i) 0) fun k hk => by
      simp only [rowAccW, show ¬ i + k < i by omega_arith, show i + k < i + w by omega_arith, ite_false,
        ite_true, Nat.add_sub_cancel_left]]
    simp only [rowAccW, show ¬ i + w < i by omega_arith, Nat.lt_irrefl, ite_false]
  have e3 : val16 (rowC acc a b i) w = a i * val16 b w + val16 (fun k => acc (i + k)) w := by
    rw [← val16_cmul, ← val16_add]; rfl
  have hc := chain_val (rowC acc a b i) 0 w
  rw [Nat.add_zero, e3] at hc
  rw [val16_append _ i (w + 1), e1, e2, hc, val16_succ a i, Nat.add_mul, ← hv, val16_append acc i w,
    Nat.mul_add, Nat.mul_assoc]
  omega_arith

theorem rowAccW_lt {w : Nat} {acc a b : Nat → Nat} {i : Nat} (hacc : ∀ k < i, acc k < 65536)
    (hc : ∀ j < w, rowC acc a b i j + 65536 ≤ 2 ^ 32) :
    ∀ k < i + (w + 1), rowAccW w acc a b i k < 65536 := by
  intro k _
  simp only [rowAccW]
  split
  · exact hacc k ‹_›
  · split
    · exact out_lt _ _ _
    · exact chain_lt hc (by decide) w (Nat.le_refl _)

end VG.Proof.Ed25519.Arm
end

/-! The carry pass that subtracts the subgroup order. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {b : BitVec 32}

theorem scalarSubtractPass_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) SR)
    (h5 : (s.gpr .r5).toNat = 1) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block (pass .r0 SD scalarSubtractSrc)) s
      (PassInv .r0 SD s (fun k => limb s.mem (State.addr b) SR k + scalarComplement k) 1 16) := by
  have hR : SR = 256 := rfl
  have hT : SD = 320 := rfl
  refine pass_ok (by decide) (by decide) (by rw [hc.r0]; have := hc.fit; omega_using [hT, this])
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega_using [hT, hk])) h6 h5
    (fun k hk => by have := hl k hk; have := scalarComplement_lt k; omega_arith) (by decide) ?_
  intro k hk t ht
  have hct := hc.of_rest ht.rest (by decide)
  unfold scalarSubtractSrc
  refine ldr0_ok hct (by omega_using [hR, hk]) fun u hu => wp_movw fun v hv =>
    wp_dp (op2_reg _ _) fun w hw => WP.block_nil ?_
  have he : (u.gpr .r3).toNat = limb s.mem (State.addr b) SR k := by
    rw [hu.gpr]
    exact wd_frame ht.frame fun r hr => by
      rw [List.mem_singleton.mp hr, hc.r0]
      exact Offset.disjoint _ (.inl (by omega_using [hR, hT, hk])) (by omega_using [hR, hk]) (by omega_using [hT, hk])
  have hc2 : (v.gpr .r2).toNat = scalarComplement k := by
    rw [hv.gpr, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (scalarComplement_lt k)]
    exact Nat.mod_eq_of_lt (by have := scalarComplement_lt k; omega_using [this])
  refine ⟨?_, (hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide))), by
    rw [hw.mem, hv.mem, hu.mem]⟩
  rw [hw.gpr]
  show (v.gpr .r3 + v.gpr .r2).toNat = _
  rw [hv.other .r3 (by decide), toNat_add_lt (by rw [he, hc2]; have := hl k hk; have := scalarComplement_lt k; omega_arith), he, hc2]

end VG.Proof.Ed25519.Arm
