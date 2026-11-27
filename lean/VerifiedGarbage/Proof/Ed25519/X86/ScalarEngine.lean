module

public import VerifiedGarbage.Proof.Ed25519.X86.CommonContract
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L)

/-! ## The arithmetic of the reduction

For `x < 2⁵¹²`, `μ = ⌊2⁵¹² / L⌋`, `q₁ = ⌊x / 2²²⁴⌋` and `q₃ = ⌊q₁ μ / 2²⁸⁸⌋`: `q₃ L ≤ x < q₃ L + 3 L`
(`barrett_low`, `barrett_high`), so `x - q₃ L` is below `2²⁵⁶` and is what its low 256 bits give
(`barrett_diff`). -/

theorem scalarMu_val : 2 ^ 256 * 2 ^ 256 / L = 1852673427797059126777135760139006525645217721299241702126143248052143860224795 := by decide

theorem scalarL_val : L = 7237005577332262213973186563042994240857116359379907606001950938285454250989 := by decide

theorem scalarMu_num : num (fun k => (scalarMu k).toNat) 9 = 1852673427797059126777135760139006525645217721299241702126143248052143860224795 := by decide

theorem scalarL_num : num (fun k => (scalarL k).toNat) 8 = 7237005577332262213973186563042994240857116359379907606001950938285454250989 := by decide

theorem barrett_carry {X lo q1 Qv a : Nat} (hX : X < 2 ^ 256 * 2 ^ 256) (hq : X = lo + 2 ^ 224 * q1)
    (hQ : Qv + 2 ^ 256 * 2 ^ 256 * 2 ^ 64 * a = q1 * 1852673427797059126777135760139006525645217721299241702126143248052143860224795) : a = 0 := by
  omega

theorem barrett_low {X lo q1 qlo q3 : Nat} (hq : X = lo + 2 ^ 224 * q1)
    (hQ : q1 * 1852673427797059126777135760139006525645217721299241702126143248052143860224795 = qlo + 2 ^ 256 * 2 ^ 32 * q3) : q3 * 7237005577332262213973186563042994240857116359379907606001950938285454250989 ≤ X := by
  omega

theorem barrett_high {X lo q1 qlo q3 : Nat} (hX : X < 2 ^ 256 * 2 ^ 256) (hq : X = lo + 2 ^ 224 * q1)
    (hlo : lo < 2 ^ 224) (hQ : q1 * 1852673427797059126777135760139006525645217721299241702126143248052143860224795 = qlo + 2 ^ 256 * 2 ^ 32 * q3) (hqlo : qlo < 2 ^ 256 * 2 ^ 32) :
    X < q3 * 7237005577332262213973186563042994240857116359379907606001950938285454250989 + 3 * 7237005577332262213973186563042994240857116359379907606001950938285454250989 := by
  omega

theorem barrett_diff {X xl hi q3 g gt Pv c H Rv c' D : Nat} (hX : X = xl + 2 ^ 256 * hi)
    (hD : X = D + q3 * 7237005577332262213973186563042994240857116359379907606001950938285454250989) (hDlt : D < 2 ^ 256) (hg : q3 = g + 2 ^ 256 * gt)
    (hP : Pv + 2 ^ 256 * c + 2 ^ 256 * H = g * 7237005577332262213973186563042994240857116359379907606001950938285454250989) (hPv : Pv < 2 ^ 256)
    (hR : Rv + 2 ^ 256 * c' = xl + (2 ^ 256 - 1 - Pv) + 1) (hRv : Rv < 2 ^ 256) : Rv = D := by
  omega

/-- The low 256 bits of `x - q₃ L` are `x - q₃ L`, a number below `3 L` in `x`'s class. -/
theorem barrett_value {X xl hi lo q1 Qv a qlo q3 g gt Pv c H Rv c' : Nat}
    (hX : X = xl + 2 ^ 256 * hi) (hxl : xl < 2 ^ 256) (hhi : hi < 2 ^ 256)
    (hq : X = lo + 2 ^ 224 * q1) (hlo : lo < 2 ^ 224)
    (hQ : Qv + 2 ^ 256 * 2 ^ 256 * 2 ^ 64 * a = q1 * (2 ^ 256 * 2 ^ 256 / L))
    (hQs : Qv = qlo + 2 ^ 256 * 2 ^ 32 * q3) (hqlo : qlo < 2 ^ 256 * 2 ^ 32)
    (hg : q3 = g + 2 ^ 256 * gt)
    (hP : Pv + 2 ^ 256 * c + 2 ^ 256 * H = g * L) (hPv : Pv < 2 ^ 256)
    (hR : Rv + 2 ^ 256 * c' = xl + (2 ^ 256 - 1 - Pv) + 1) (hRv : Rv < 2 ^ 256) :
    Rv < 3 * L ∧ Rv % L = X % L := by
  rw [scalarMu_val] at hQ
  rw [scalarL_val] at hP ⊢
  have hXlt : X < 2 ^ 256 * 2 ^ 256 := by omega_using [hX, hxl, hhi]
  obtain rfl := barrett_carry hXlt hq hQ
  rw [Nat.mul_zero, Nat.add_zero, hQs] at hQ
  have low := barrett_low hq hQ.symm
  have high := barrett_high hXlt hq hlo hQ.symm hqlo
  obtain ⟨D, hD⟩ : ∃ D, X = D + q3 * 7237005577332262213973186563042994240857116359379907606001950938285454250989 := ⟨X - q3 * 7237005577332262213973186563042994240857116359379907606001950938285454250989, by omega_using [low]⟩
  have hDlt : D < 3 * 7237005577332262213973186563042994240857116359379907606001950938285454250989 := by omega_using [hD, high]
  obtain rfl := barrett_diff hX hD (by omega_using [hDlt]) hg hP hPv hR hRv
  exact ⟨hDlt, by rw [hD, Nat.add_mul_mod_self_right]⟩

/-- Two subtractions of `L`, each only from a number that is not below it, reduce a number below `3 L`. -/
theorem condSub_twice {r : Nat} (h : r < 3 * L) :
    (if L ≤ (if L ≤ r then r - L else r) then (if L ≤ r then r - L else r) - L
      else (if L ≤ r then r - L else r)) = r % L := by
  have hp := order_pos
  by_cases h₁ : L ≤ r
  · simp only [h₁, ↓reduceIte]
    by_cases h₂ : L ≤ r - L
    · simp only [h₂, ↓reduceIte]
      rw [Nat.mod_eq_sub_mod h₁, Nat.mod_eq_sub_mod h₂, Nat.mod_eq_of_lt (by omega_using [h, h₁, h₂])]
    · simp only [h₂, ↓reduceIte]
      rw [Nat.mod_eq_sub_mod h₁, Nat.mod_eq_of_lt (by omega_using [h₂])]
  · simp only [h₁, ↓reduceIte]
    exact (Nat.mod_eq_of_lt (by omega_using [h₁])).symm

/-! ## Words -/

/-- A number's words from `a` on, above its first `a`. -/
theorem num_split (f : Nat → Nat) (a b : Nat) :
    num f (a + b) = num f a + (2 ^ 32) ^ a * num (fun k => f (a + k)) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, num_succ, ih, num_succ, Nat.mul_add, Nat.pow_add, Nat.mul_assoc, Nat.add_assoc]

/-- Product scanning of nine words by nine. -/
theorem prod_identity9 (fa fb : Nat → Nat) :
    num (fun k => (((List.range 9).filter fun i => i ≤ k && k - i < 9).map fun i =>
      fa i * fb (k - i)).sum) 18 = num fa 9 * num fb 9 := by
  simp only [X25519.X86.num_eq_numB]
  generalize 2 ^ 32 = B
  simp only [X25519.X86.numB, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.filter_cons, List.filter_nil]
  simp only [Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceLT, Nat.zero_le, Nat.le_refl, decide_true, decide_false,
    Bool.and_self, Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  grind

/-- Terms that are zero may be left out of a sum. -/
theorem sum_filter_zero (f : Nat → Nat) (p q : Nat → Bool) :
    ∀ l : List Nat, (∀ i ∈ l, p i = true → q i = false → f i = 0) →
      ((l.filter fun i => p i && q i).map f).sum = ((l.filter p).map f).sum
  | [], _ => rfl
  | i :: l, h => by
    have ih := sum_filter_zero f p q l fun j hj => h j (List.mem_cons_of_mem _ hj)
    have hi := h i List.mem_cons_self
    cases hp : p i <;> cases hq : q i <;>
      simp only [List.filter_cons, hp, hq, Bool.and_true, Bool.and_false, ↓reduceIte,
        Bool.false_eq_true, List.map_cons, List.sum_cons, ih]
    rw [hi hp hq, Nat.zero_add]

/-! ## The engine -/

theorem scalarQTerms_colv (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (scalarQTerms k) = (((List.range 9).filter fun i => i ≤ k && k - i < 9).map fun i =>
      wv m x (156 + 4 * i) * (scalarMu (k - i)).toNat).sum := by
  simp only [colv, scalarQTerms, List.map_map]; rfl

theorem scalarPTerms_colv (m : Mem) (x : BitVec 32) {k : Nat} (hk : k < 8) :
    colv m x (scalarPTerms k) = (((List.range 8).filter fun i => i ≤ k && k - i < 8).map fun i =>
      wv m x (scalarQ + 36 + 4 * i) * (scalarL (k - i)).toNat).sum := by
  have e : colv m x (scalarPTerms k) =
      (((List.range 8).filter fun i => (decide (i ≤ k) && decide (k - i < 8)) &&
        (decide (k - i < 4) || k - i == 7)).map fun i =>
        wv m x (scalarQ + 36 + 4 * i) * (scalarL (k - i)).toNat).sum := by
    simp only [colv, scalarPTerms, List.map_map]
    refine congrArg List.sum (congr (congrArg List.map rfl) (List.filter_congr fun i hi => ?_))
    have hi' := List.mem_range.mp hi
    have : decide (k - i < 8) = true := decide_eq_true (by omega_using [hk])
    rw [this, Bool.and_true]
  rw [e]
  refine sum_filter_zero _ _ _ _ fun i hi hp hq => ?_
  have hi' := List.mem_range.mp hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at hp hq
  have z : (scalarL (k - i)).toNat = 0 := by
    rcases (by omega_using [hp, hq] : k - i = 4 ∨ k - i = 5 ∨ k - i = 6) with h | h | h <;> rw [h] <;> decide
  rw [z, Nat.mul_zero]

theorem scalarEngine_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa scalarEngine s fun t => ScalarKeep s t ∧ Frame (scalarBodyFrame x) s.mem t.mem ∧
      fe t.mem x scalarR = Spec.Ed25519.decodeLE (scalarInput s.mem x) % Spec.Ed25519.L := by
  have hfit := hc.fit
  have hQo : scalarQ = 384 := rfl
  have hPo : scalarP = 480 := rfl
  have hRo : scalarR = 64 := rfl
  unfold scalarEngine
  simp only [List.append_assoc]
  -- `q₁ μ`
  refine WP.block_append (WP.mono zeroAcc_ok fun u₀ ⟨k₀, m₀, a₀⟩ => ?_)
  refine WP.block_append (WP.mono (cols_ok (k₀.ctx hc) scalarQTerms 18 (by decide)
    (fun k hk t ht d hd => ?_) (fun k hk => ?_) (by rw [a₀]; decide)) fun u₁ ⟨k₁, f₁, e₁, _⟩ => ?_)
  · simp only [scalarQTerms, List.mem_map, List.mem_filter, List.mem_range] at ht
    obtain ⟨i, ⟨hi, -⟩, rfl⟩ := ht
    simp only [treads, List.mem_singleton] at hd
    subst hd
    exact ⟨by omega_using [hi], Or.inl (by omega_using [hi, hQo])⟩
  · have hl : (scalarQTerms k).length ≤ 9 := by
      simp only [scalarQTerms, List.length_map]
      exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    have h1 := colv_le_len (m := u₀.mem) (x := x) (B := 2 ^ 64) (ts := scalarQTerms k) fun t ht => by
      simp only [scalarQTerms, List.mem_map] at ht
      obtain ⟨i, -, rfl⟩ := ht
      exact Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt (wv_lt _ _ _)) (Nat.le_of_lt (BitVec.isLt _))) (by decide)
    have h2 := Nat.mul_le_mul_right (2 ^ 64) hl
    omega_using [h1, h2]
  -- `q₃ L`
  refine WP.block_append (WP.mono zeroAcc_ok fun u₂ ⟨k₂, m₂, a₂⟩ => ?_)
  have c₂ := k₂.ctx (k₁.ctx (k₀.ctx hc))
  refine WP.block_append (WP.mono (cols_ok c₂ scalarPTerms 8 (by decide)
    (fun k hk t ht d hd => ?_) (fun k hk => ?_) (by rw [a₂]; decide)) fun u₃ ⟨k₃, f₃, e₃, _⟩ => ?_)
  · simp only [scalarPTerms, List.mem_map, List.mem_filter, List.mem_range] at ht
    obtain ⟨i, ⟨hi, -⟩, rfl⟩ := ht
    simp only [treads, List.mem_singleton] at hd
    subst hd
    exact ⟨by omega_using [hi, hQo], Or.inl (by omega_using [hi, hQo, hPo])⟩
  · have hl : (scalarPTerms k).length ≤ 8 := by
      simp only [scalarPTerms, List.length_map]
      exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    have h1 := colv_le_len (m := u₂.mem) (x := x) (B := 2 ^ 64) (ts := scalarPTerms k) fun t ht => by
      simp only [scalarPTerms, List.mem_map] at ht
      obtain ⟨i, -, rfl⟩ := ht
      exact Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt (wv_lt _ _ _)) (Nat.le_of_lt (BitVec.isLt _))) (by decide)
    have h2 := Nat.mul_le_mul_right (2 ^ 64) hl
    omega_using [h1, h2]
  -- `x - q₃ L`
  refine WP.block_append (WP.mono zeroAcc_ok fun u₄ ⟨k₄, m₄, a₄⟩ => ?_)
  have c₄ := k₄.ctx (k₃.ctx c₂)
  refine WP.block_append (WP.mono (cols_ok c₄ scalarDiffTerms 8 (by decide)
    (fun k hk t ht d hd => ?_) (fun k hk => ?_) (by rw [a₄]; decide)) fun u₅ ⟨k₅, f₅, e₅, _⟩ => ?_)
  · have hm : t = .addM (128 + 4 * k) ∨ t = .addNot (scalarP + 4 * k) ∨ t = .addI 1 := by
      simp only [scalarDiffTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with (rfl | rfl) | ht
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · split at ht
        · exact .inr (.inr (List.mem_singleton.mp ht))
        · exact absurd ht List.not_mem_nil
    rcases hm with rfl | rfl | rfl
    · simp only [treads, List.mem_singleton] at hd; subst hd
      exact ⟨by omega_using [hk], Or.inr (by omega_using [hRo])⟩
    · simp only [treads, List.mem_singleton] at hd; subst hd
      exact ⟨by omega_using [hk, hPo], Or.inr (by omega_using [hRo, hPo])⟩
    · simp only [treads, List.not_mem_nil] at hd
  · have hl : (scalarDiffTerms k).length ≤ 3 := by
      simp only [scalarDiffTerms, List.length_append, List.length_cons, List.length_nil]
      split <;> simp
    have h1 := colv_le_len (m := u₄.mem) (x := x) (B := 2 ^ 32) (ts := scalarDiffTerms k) fun t ht => by
      simp only [scalarDiffTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with (rfl | rfl) | ht
      · exact Nat.le_of_lt (wv_lt _ _ _)
      · simp only [tval]; omega_using []
      · split at ht
        · rw [List.mem_singleton.mp ht]; exact (by decide : (1 : BitVec 32).toNat ≤ 2 ^ 32)
        · exact absurd ht List.not_mem_nil
    have h2 := Nat.mul_le_mul_right (2 ^ 32) hl
    omega_using [h1, h2]
  -- `L` subtracted twice
  have c₅ := k₅.ctx c₄
  refine WP.block_append (WP.mono (scalarCondSub_ok c₅) fun u₆ ⟨k₆, f₆, e₆⟩ => ?_)
  refine WP.mono (scalarCondSub_ok (k₆.ctx c₅)) fun t ⟨k₇, f₇, e₇⟩ => ?_
  -- The frames.
  have f₁' : Frame (scalarBodyFrame x) s.mem u₂.mem := by
    rw [m₂, ← m₀]; exact f₁.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self
  have f₃' : Frame (scalarBodyFrame x) u₂.mem u₄.mem := by
    rw [m₄]; exact f₃.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have f₅' : Frame (scalarBodyFrame x) u₄.mem u₅.mem := f₅.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have f₆' : Frame (scalarBodyFrame x) u₅.mem u₆.mem := f₆.mono fun r hr =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  have f₇' : Frame (scalarBodyFrame x) u₆.mem t.mem := f₇.mono fun r hr =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  refine ⟨(Keep.scalar k₀).trans ((Keep.scalar k₁).trans ((Keep.scalar k₂).trans ((Keep.scalar k₃).trans
    ((Keep.scalar k₄).trans ((Keep.scalar k₅).trans ((Keep.scalar k₆).trans (Keep.scalar k₇))))))),
    f₁'.trans (f₃'.trans (f₅'.trans (f₆'.trans f₇'))), ?_⟩
  -- The input, and the words the later columns read.
  let w : Nat → Nat := fun k => wv s.mem x (128 + 4 * k)
  have hw : ∀ k, w k < 2 ^ 32 := fun k => wv_lt _ _ _
  have hX : Spec.Ed25519.decodeLE (scalarInput s.mem x) = num w 16 := scalarInput_num s.mem hfit
  have wQ : ∀ d, d + 4 ≤ scalarQ → wd u₁.mem x d = wd s.mem x d := fun d hd => by
    rw [← m₀]; exact wd_frame1 f₁ hfit (by decide) (by omega_using [hd, hQo]) (Or.inl hd)
  have wP : ∀ d, d + 4 ≤ scalarP → wd u₃.mem x d = wd u₁.mem x d := fun d hd => by
    rw [← m₂]; exact wd_frame1 f₃ hfit (by decide) (by omega_using [hd, hPo]) (Or.inl hd)
  -- `q₁ μ`
  have vQ : num (fun k => wv u₁.mem x (scalarQ + 4 * k)) 18 + 2 ^ 256 * 2 ^ 256 * 2 ^ 64 * acc u₁ =
      num (fun i => w (7 + i)) 9 * (2 ^ 256 * 2 ^ 256 / L) := by
    rw [a₀, Nat.zero_add, m₀] at e₁
    rw [show (2 : Nat) ^ 256 * 2 ^ 256 * 2 ^ 64 = (2 ^ 32) ^ 18 by decide, e₁, scalarMu_val, ← scalarMu_num,
      ← prod_identity9]
    exact num_congr fun k _ => by
      rw [scalarQTerms_colv]
      exact congrArg List.sum (List.map_congr_left fun i _ => by
        show wv s.mem x (156 + 4 * i) * _ = wv s.mem x (128 + 4 * (7 + i)) * _
        rw [show 128 + 4 * (7 + i) = 156 + 4 * i by omega_using []])
  -- `q₃ L`
  let g : Nat → Nat := fun i => wv u₁.mem x (scalarQ + 36 + 4 * i)
  have hg : ∀ i, g i < 2 ^ 32 := fun i => wv_lt _ _ _
  have vP : ∃ H, fe u₃.mem x scalarP + 2 ^ 256 * acc u₃ + 2 ^ 256 * H = num g 8 * L := by
    rw [a₂, Nat.zero_add, m₂] at e₃
    refine ⟨num (fun k => (((List.range 8).filter fun i => i ≤ 8 + k && 8 + k - i < 8).map fun i =>
      g i * (scalarL (8 + k - i)).toNat).sum) 8, ?_⟩
    have full := prod_identity g fun j => (scalarL j).toNat
    rw [num_16, scalarL_num, ← scalarL_val] at full
    rw [← full]
    have low : num (fun k => colv u₁.mem x (scalarPTerms k)) 8 =
        num (fun k => (((List.range 8).filter fun i => i ≤ k && k - i < 8).map fun i =>
          g i * (scalarL (k - i)).toNat).sum) 8 := num_congr fun k hk => scalarPTerms_colv _ _ hk
    rw [← low, ← e₃]
    show fe u₃.mem x scalarP + 2 ^ 256 * acc u₃ + _ = fe u₃.mem x scalarP + (2 ^ 32) ^ 8 * acc u₃ + _
    rfl
  -- `x - q₃ L`
  have vR : fe u₅.mem x scalarR + 2 ^ 256 * acc u₅ =
      num w 8 + (2 ^ 256 - 1 - fe u₃.mem x scalarP) + 1 := by
    rw [a₄, Nat.zero_add, m₄] at e₅
    have hcol : num (fun k => colv u₃.mem x (scalarDiffTerms k)) 8 =
        num (fun k => w k + (2 ^ 32 - 1 - wv u₃.mem x (scalarP + 4 * k)) + if k = 0 then 1 else 0) 8 :=
      num_congr fun k hk => by
        have ew : wv u₃.mem x (128 + 4 * k) = w k :=
          congrArg BitVec.toNat ((wP _ (by omega_using [hk, hPo])).trans (wQ _ (by omega_using [hk, hQo])))
        simp only [colv, scalarDiffTerms, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil, tval, Nat.add_zero, ew]
        split
        · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tval]; rfl
        · simp only [List.map_nil, List.sum_nil]
    rw [hcol, num_add, num_add, X25519.X86.num_not (fun k _ => wv_lt _ _ _)] at e₅
    exact e₅
  -- The value.
  have s16 := num_split w 8 8
  have s7 := num_split w 7 9
  have sQ := num_split (fun k => wv u₁.mem x (scalarQ + 4 * k)) 9 9
  have sg := num_split g 8 1
  have gQ : num (fun k => wv u₁.mem x (scalarQ + 4 * (9 + k))) 9 = num g 9 := num_congr fun k _ => by
    show wv u₁.mem x (scalarQ + 4 * (9 + k)) = wv u₁.mem x (scalarQ + 36 + 4 * k)
    rw [show scalarQ + 4 * (9 + k) = scalarQ + 36 + 4 * k by omega_using []]
  rw [gQ] at sQ
  obtain ⟨H, vP⟩ := vP
  have b := barrett_value (X := num w 16) (xl := num w 8) (hi := num (fun k => w (8 + k)) 8) (lo := num w 7)
    (q1 := num (fun i => w (7 + i)) 9) (Qv := num (fun k => wv u₁.mem x (scalarQ + 4 * k)) 18) (a := acc u₁)
    (qlo := num (fun k => wv u₁.mem x (scalarQ + 4 * k)) 9) (q3 := num g 9) (g := num g 8)
    (gt := num (fun k => g (8 + k)) 1) (Pv := fe u₃.mem x scalarP) (c := acc u₃) (H := H)
    (Rv := fe u₅.mem x scalarR) (c' := acc u₅) s16
    (X25519.X86.num_lt fun k _ => hw k) (X25519.X86.num_lt fun k _ => hw (8 + k)) s7
    (X25519.X86.num_lt fun k _ => hw k) vQ sQ (X25519.X86.num_lt fun k _ => wv_lt _ _ _) sg vP (fe_lt _ _ _) vR
    (fe_lt _ _ _)
  rw [hX, e₇, e₆, ← b.2]
  exact condSub_twice b.1

theorem Saved.scalarEngine {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hk : ScalarKeep s t)
    (hf : Frame (scalarBodyFrame x) s.mem t.mem) : Saved s₀ x t := by
  apply h.of_frame hk hf
  · intro r hr
    simp only [scalarBodyFrame, scalarFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> refine .inl ?_ <;> rw [scR_eq] <;>
      exact sub_sub hx (by decide) (by decide) (by decide)
  · have hR : scalarR = 64 := rfl
    have hT : T = 864 := rfl
    have hQ : scalarQ = 384 := rfl
    have hP : scalarP = 480 := rfl
    intro p hp r hr
    have hj := savedSlots_bound p hp
    simp only [scalarBodyFrame, scalarFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact sub_disj (by omega_using [hx, hj]) (by omega_using [hx, hR, hT, hQ, hP])
        (Or.inl (by omega_using [hj, hR, hT, hQ, hP]))
end VG.Proof.Ed25519.X86
