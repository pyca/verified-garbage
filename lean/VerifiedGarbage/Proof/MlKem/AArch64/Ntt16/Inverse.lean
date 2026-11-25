module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Trace
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Arith
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Forward
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Trace

/-!
# The inverse NTT: its values, and its code

`iv F l` is the coefficients after `l` layers, and `raw` the sums and differences of a layer before
its products, of which the code computes exactly these halfwords (`code_run`), whatever the order it
computes them in. They represent the coefficients of the inverse NTT (`rep_lo`, and times `128⁻¹`
from the fourth layer on, `rep_hi`), within bounds that keep every sum and difference in range.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16.Inverse

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16 VG.Impl.MlKem.AArch64.Ntt16.Inverse VG.Proof.MlKem.AArch64.Ntt16
open VG.Spec.MlKem (Poly Zq)

/-- Coefficient `i` is the upper input and output of its butterfly of layer `l`. -/
def Low (l i : Nat) : Prop := i % (2 * (2 <<< l)) < 2 <<< l

instance (l i : Nat) : Decidable (Low l i) := inferInstanceAs (Decidable (_ < _))

/-- What is subtracted from coefficient `i`, a sum, in layer `l`. -/
def ofsN (l i : Nat) : Nat := if l = 3 ∧ i % 16 < 2 then 26632 else 0

/-- The constant that multiplies coefficient `i` in layer `l`. -/
def mulN (l i : Nat) : Nat :=
  let z := Impl.MlKem.AArch64.Ntt16.zeta (128 >>> l - 1 - i / (2 * (2 <<< l)))
  if l = 3 then if Low l i then 3303 else z * 3303 % 3329 else z

def mulB (l i : Nat) : BitVec 16 := BitVec.ofNat 16 (cen (mulN l i))
def mulT (l i : Nat) : BitVec 16 := BitVec.ofNat 16 (quo (mulN l i))

/-- The sums and differences of layer `l` of `g`. -/
def raw (l : Nat) (g : Nat → BitVec 16) (i : Nat) : BitVec 16 :=
  if Low l i then g i + g (i + 2 <<< l) - BitVec.ofNat 16 (ofsN l i) else g i - g (i - 2 <<< l)

/-- Layer `l`, of its sums and differences `r`. -/
def out (l : Nat) (r : Nat → BitVec 16) (i : Nat) : BitVec 16 :=
  if l = 6 then if Low l i then canon (r i) else pos (red (r i) (mulB l i) (mulT l i))
  else if l ≠ 3 ∧ Low l i then r i else red (r i) (mulB l i) (mulT l i)

/-- The coefficients after the first `l` layers, of the coefficients `F`. -/
def iv (F : Nat → BitVec 16) : Nat → Nat → BitVec 16
  | 0 => F
  | l + 1 => out l (raw l (iv F l))

/-- Value `512 l + i`: coefficient `i` after `l` layers; value `512 l + 256 + i`: its sum or
difference in the next. -/
def value (F : Nat → BitVec 16) (n : Nat) : BitVec 16 :=
  if n / 256 % 2 = 0 then iv F (n / 512) (n % 256) else raw (n / 512) (iv F (n / 512)) (n % 256)

/-- `Low`, of a value. -/
def lowN (n : Nat) : Bool := Nat.blt (n % 256 % (2 * (2 <<< (n / 512)))) (2 <<< (n / 512))

/-- The values `u` and `v` are the inputs of a butterfly. -/
def pairOk (u v : Nat) : Bool :=
  Nat.beq (u / 256 % 2) 0 && Nat.blt (u / 512) 7 && Nat.beq v (u + 2 <<< (u / 512)) && lowN u

/-- `c` is what is subtracted from the sum that replaces `u`. -/
def ofsOk (c u : Nat) : Bool := Nat.beq c (ofsN (u / 512) (u % 256))

/-- `z` and `t` are the multiplier of the sum or difference `n`. -/
def mulOk (n z t : Nat) : Bool :=
  Nat.beq (n / 256 % 2) 1 && Nat.beq z (cen (mulN (n / 512) (n % 256))) && Nat.beq t (quo (mulN (n / 512) (n % 256)))

def dir : Dir where
  add a b := match a, b with
    | .coef us, .coef vs =>
      if all3 (fun u v _ => pairOk u v) 8 us vs vs then
        if all3 (fun u _ _ => !Nat.beq (u / 512) 3 && !Nat.beq (u / 512) 6) 8 us us us then some (.coef (next 512 us))
        else if all3 (fun u _ _ => ofsOk 0 u) 8 us us us then some (.coef (next 256 us))
        else some (.sum us vs)
      else none
    | .prod ns zs ts, .fix ms ws xs =>
      if decide (ms = ns) && decide (ws = zs) && decide (xs = ts) && all3 mulOk 8 ns zs ts &&
          all3 (fun n _ _ => Nat.beq (n / 512) 6 && !lowN n) 8 ns ns ns then
        some (.coef (next 256 ns)) else none
    | _, _ => none
  sub a b := match a, b with
    | .coef vs, .coef us => if all3 (fun u v _ => pairOk u v) 8 us vs vs then some (.coef (next 256 vs)) else none
    | .sum us vs, .lit cs =>
      if all3 (fun u v _ => pairOk u v) 8 us vs vs && all3 (fun c u _ => ofsOk c u) 8 cs us us then
        some (.coef (next 256 us)) else none
    | _, _ => none
  prod ns zs ts :=
    if all3 (fun n _ _ => Nat.beq (n / 512) 6) 8 ns ns ns then some (.prod ns zs ts)
    else if all3 mulOk 8 ns zs ts &&
        all3 (fun n _ _ => Nat.blt (n / 512) 6 && (Nat.beq (n / 512) 3 || !lowN n)) 8 ns ns ns then
      some (.coef (next 256 ns)) else none
  canon ns :=
    if all3 (fun n _ _ => Nat.beq (n / 256) 13 && lowN n) 8 ns ns ns then some (.coef (next 256 ns)) else none

/-! ## The values -/

/-- What the lower output of a butterfly of layer `l` is. -/
theorem lower_facts {l i : Nat} (hl : l < 7) (hi : Low l i) (h : i < 256) :
    i + 2 <<< l < 256 ∧ ¬ Low l (i + 2 <<< l) := by
  simp only [Low] at hi ⊢
  match l, hl with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ =>
    simp only [Nat.reduceShiftLeft, Nat.reduceMul] at hi ⊢
    refine ⟨?_, ?_⟩ <;> omega_using [hi, h]
  | _ + 7, h => exact absurd h (by omega_using [])

theorem lowN_iff {n : Nat} : lowN n = true ↔ Low (n / 512) (n % 256) := by simp only [lowN, Nat.blt_eq, Low]

theorem lowN_false {n : Nat} (h : (!lowN n) = true) : ¬ Low (n / 512) (n % 256) := fun hl => by
  rw [lowN_iff.2 hl] at h; cases h

theorem pairOk_spec {u v : Nat} (h : pairOk u v = true) :
    u / 256 % 2 = 0 ∧ u / 512 < 7 ∧ Low (u / 512) (u % 256) ∧ v / 256 = u / 256 ∧ v / 512 = u / 512 ∧
      v % 256 = u % 256 + 2 <<< (u / 512) := by
  simp only [pairOk, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h1 := Nat.eq_of_beq_eq_true h1
  have h3 := Nat.eq_of_beq_eq_true h3
  have h4 := lowN_iff.1 h4
  have := (lower_facts h2 h4 (Nat.mod_lt _ (by decide))).1
  generalize 2 <<< (u / 512) = d at *
  refine ⟨h1, h2, h4, ?_, ?_, ?_⟩ <;> omega_using [h3, this]

/-- A sum. -/
theorem value_sum {u v : Nat} (h : pairOk u v = true) (F : Nat → BitVec 16) :
    value F (u + 256) = value F u + value F v - BitVec.ofNat 16 (ofsN (u / 512) (u % 256)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairOk_spec h
  simp only [value, show (u + 256) / 256 % 2 = 1 by omega_using [h1], show (u + 256) / 512 = u / 512 by omega_using [h1],
    show (u + 256) % 256 = u % 256 by omega_using [], h4, h5, h1, h6, show ¬ (1 = 0) by decide, ↓reduceIte]
  rw [raw, ite_eq_left h3]

/-- A difference. -/
theorem value_diff {u v : Nat} (h : pairOk u v = true) (F : Nat → BitVec 16) :
    value F (v + 256) = value F v - value F u := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pairOk_spec h
  simp only [value, show (v + 256) / 256 % 2 = 1 by omega_using [h1, h4], show (v + 256) / 512 = u / 512 by omega_using [h1, h4],
    show (v + 256) % 256 = v % 256 by omega_using [], h4, h5, h1, h6, show ¬ (1 = 0) by decide, ↓reduceIte]
  rw [raw, ite_eq_right (lower_facts h2 h3 (Nat.mod_lt _ (by decide))).2, Nat.add_sub_cancel]

/-- What follows a sum or difference. -/
theorem value_out {n : Nat} (h : n / 256 % 2 = 1) (F : Nat → BitVec 16) :
    value F (n + 256) = out (n / 512) (raw (n / 512) (iv F (n / 512))) (n % 256) ∧
      value F n = raw (n / 512) (iv F (n / 512)) (n % 256) := by
  constructor
  · simp only [value, show (n + 256) / 256 % 2 = 0 by omega_using [h], show (n + 256) / 512 = n / 512 + 1 by omega_using [h],
      show (n + 256) % 256 = n % 256 by omega_using [], ↓reduceIte, iv]
  · simp only [value, h, show ¬ (1 = 0) by decide, ↓reduceIte]

theorem mulOk_spec {n z t : Nat} (h : mulOk n z t = true) : n / 256 % 2 = 1 ∧
    BitVec.ofNat 16 z = mulB (n / 512) (n % 256) ∧ BitVec.ofNat 16 t = mulT (n / 512) (n % 256) := by
  simp only [mulOk, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h1, by rw [Nat.eq_of_beq_eq_true h2]; rfl, by rw [Nat.eq_of_beq_eq_true h3]; rfl⟩

theorem dir_sound (F : Nat → BitVec 16) : dir.Sound (value F) where
  add := by
    intro a b c h e he
    simp only [dir] at h
    split at h
    · rename_i us vs
      split at h
      · rename_i hp
        have hl := (all3_length hp).1
        have hpe := all3_get hp e he
        have hs := value_sum hpe F
        have hf := pairOk_spec hpe
        split at h
        · rename_i hn
          cases h
          have hn := all3_get hn e he
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hn
          have n3 := Nat.ne_of_beq_eq_false hn.1
          have n6 := Nat.ne_of_beq_eq_false hn.2
          simp only [Val.lane]
          rw [getD_next (by omega_using [hl, he])]
          generalize us.getD e 0 = u at *
          generalize vs.getD e 0 = v at *
          have hh : (u + 256) / 256 % 2 = 1 ∧ (u + 256) / 512 = u / 512 ∧ (u + 256) % 256 = u % 256 := by
            refine ⟨?_, ?_, ?_⟩ <;> omega_using [hf.1]
          obtain ⟨o1, o2⟩ := value_out hh.1 F
          rw [show u + 512 = u + 256 + 256 from rfl, o1, hh.2.1, hh.2.2, out, ite_eq_right n6, ite_eq_left ⟨n3, hf.2.2.1⟩]
          rw [hh.2.1, hh.2.2] at o2
          rw [← o2, hs, ofsN, ite_eq_right (fun hc => n3 hc.1)]
          exact BitVec.sub_zero _
        · split at h
          · rename_i ho
            cases h
            simp only [Val.lane]
            rw [getD_next (by omega_using [hl, he]), hs, ← Nat.eq_of_beq_eq_true (all3_get ho e he)]
            exact BitVec.sub_zero _
          · cases h; rfl
      · cases h
    · rename_i ns zs ts ms ws xs
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hm⟩, hn⟩ := hc
        cases h
        have hl := (all3_length hm).1
        have hn := all3_get hn e he
        simp only [Bool.and_eq_true] at hn
        obtain ⟨m1, m2, m3⟩ := mulOk_spec (all3_get hm e he)
        simp only [Val.lane, cst]
        rw [getD_next (by omega_using [hl, he]), m2, m3, (value_out m1 F).1, (value_out m1 F).2,
          out, ite_eq_left (Nat.eq_of_beq_eq_true hn.1), ite_eq_right (lowN_false hn.2)]
        rfl
      · cases h
    · cases h
  sub := by
    intro a b c h e he
    simp only [dir] at h
    split at h
    · split at h
      · rename_i vs us hp
        cases h
        simp only [Val.lane]
        rw [getD_next (by have := (all3_length hp).2; omega_using [this, he]), value_diff (all3_get hp e he) F]
      · cases h
    · rename_i us vs cs
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        cases h
        simp only [Val.lane, cst]
        rw [getD_next (by have := (all3_length hc.1).1; omega_using [this, he]), value_sum (all3_get hc.1 e he) F,
          ← Nat.eq_of_beq_eq_true (all3_get hc.2 e he)]
      · cases h
    · cases h
  prod := by
    intro ns zs ts c h e he
    simp only [dir] at h
    split at h
    · cases h; rfl
    · split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        cases h
        have hl := (all3_length hc.1).1
        have hn := all3_get hc.2 e he
        simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at hn
        obtain ⟨m1, m2, m3⟩ := mulOk_spec (all3_get hc.1 e he)
        simp only [Val.lane, cst]
        rw [getD_next (by omega_using [hl, he]), m2, m3, (value_out m1 F).1, (value_out m1 F).2, out,
          ite_eq_right (by omega_using [hn.1]), ite_eq_right]
        intro hh
        rcases hn.2 with h3 | h3
        · exact hh.1 (Nat.eq_of_beq_eq_true h3)
        · exact lowN_false h3 hh.2
      · cases h
  canon := by
    intro ns c h e he
    simp only [dir] at h
    split at h
    · rename_i hb
      cases h
      have hl := (all3_length hb).1
      have hn := all3_get hb e he
      simp only [Bool.and_eq_true] at hn
      have hn1 := Nat.eq_of_beq_eq_true hn.1
      simp only [Val.lane]
      rw [getD_next (by omega_using [hl, he])]
      obtain ⟨o1, o2⟩ := value_out (n := ns.getD e 0) (by omega_using [hn1]) F
      rw [o1, o2, out, ite_eq_left (by omega_using [hn1]), ite_eq_left (lowN_iff.1 hn.2)]
      rfl
    · cases h

/-! ## The code -/

/-- The state before the code. -/
def start : St := ⟨List.replicate 32 none, (List.range 32).map fun i => (List.range 8).map fun e => 8 * i + e⟩

/-- The polynomial after it. -/
def final : List (List Nat) := (List.range 32).map fun i => (List.range 8).map fun e => 3584 + 8 * i + e

theorem code_run : ((run dir invRows.lit body start).map fun a => decide (a.mem = final)) = some true := by
  lit_decide

/-! ## What the values represent -/

theorem mul_assoc_zq (a b c : Zq) : a * b * c = a * (b * c) := Fin.ext (by
  rw [val_mul_nat, val_mul_nat, val_mul_nat, val_mul_nat, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc])

theorem mul_comm_zq (a b : Zq) : a * b = b * a := Fin.ext (by rw [val_mul_nat, val_mul_nat, Nat.mul_comm])

theorem mul_add_zq (c a b : Zq) : c * (a + b) = c * a + c * b := Fin.ext (by
  rw [val_mul_nat, val_add_nat, val_add_nat, val_mul_nat, val_mul_nat, Nat.mul_mod_mod, ← Nat.add_mod, Nat.mul_add])

theorem mul_sub_zq (c a b : Zq) : c * (a - b) = c * a - c * b := by
  have h : a - b + b = a := Fin.ext (by
    have := val_lt_int a; have := val_lt_int b
    have := val_sub_nat a b
    have := val_add_nat (a - b) b
    omega)
  have h' := mul_add_zq c (a - b) b
  rw [h] at h'
  apply Fin.ext
  have h1 := val_lt_int (c * (a - b))
  have h2 := val_lt_int (c * b)
  have h3 := val_sub_nat (c * a) (c * b)
  have h4 := val_add_nat (c * (a - b)) (c * b)
  have h5 := val_lt_int (c * a)
  rw [← h'] at h4
  generalize (c * (a - b)).val = X at *
  generalize (c * a).val = Y at *
  generalize (c * b).val = Z at *
  omega_using [h1, h2, h3, h4, h5]

/-- Bounds on coefficient `i` after `l ≤ 3` layers. -/
def hiB (l i : Nat) : Int :=
  let m := i % 2 ^ (l + 1)
  3328 * if m < 2 then 2 ^ l else if m < 4 then 2 ^ (l - 1) else if m < 8 then 2 ^ (l - 2) else 1

def loB (l i : Nat) : Int := if i % 2 ^ (l + 1) < 2 then 0 else -hiB l i

theorem bounds : ∀ l < 3, ∀ i < 256,
    if Low l i then loB (l + 1) i ≤ loB l i + loB l (i + 2 <<< l) ∧ hiB l i + hiB l (i + 2 <<< l) ≤ hiB (l + 1) i ∧
      -32768 ≤ loB l i + loB l (i + 2 <<< l) ∧ hiB l i + hiB l (i + 2 <<< l) < 32768
    else loB (l + 1) i ≤ -3328 ∧ 3328 ≤ hiB (l + 1) i ∧
      -32768 ≤ loB l i - hiB l (i - 2 <<< l) ∧ hiB l i - loB l (i - 2 <<< l) < 32768 := by
  decide +kernel

theorem bounds3 : ∀ i < 256, if Low 3 i then
      -32768 ≤ loB 3 i + loB 3 (i + 2 <<< 3) - ofsN 3 i ∧ hiB 3 i + hiB 3 (i + 2 <<< 3) - ofsN 3 i < 32768
    else -32768 ≤ loB 3 i - hiB 3 (i - 2 <<< 3) ∧ hiB 3 i - loB 3 (i - 2 <<< 3) < 32768 := by
  decide +kernel

/-- The standard's zeta of coefficient `i` in layer `l`. -/
def zk (l i : Nat) : Zq := Proof.MlKem.zeta (256 / (2 <<< l) - 1 - i / (2 * (2 <<< l)))

theorem zk_val {l i : Nat} (hl : l < 7) :
    Impl.MlKem.AArch64.Ntt16.zeta (128 >>> l - 1 - i / (2 * (2 <<< l))) = (zk l i).val := by
  have h : 256 / (2 <<< l) = 128 >>> l ∧ 128 >>> l ≤ 128 := by
    match l, hl with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide
    | _ + 7, h => exact absurd h (by omega_using [])
  rw [zk, h.1, ← zeta_val (by omega_using [h.2])]
  rfl

theorem scaled_facts : ∀ k < 16,
    (BitVec.ofNat 16 (cen (zetaTable.getD k 0 * 3303 % 3329))).toInt % 3329 = ((zetaTable.getD k 0 * 3303 % 3329 : Nat) : Int) ∧
    -1664 ≤ 32768 * (BitVec.ofNat 16 (cen (zetaTable.getD k 0 * 3303 % 3329))).toInt -
      3329 * (BitVec.ofNat 16 (quo (zetaTable.getD k 0 * 3303 % 3329))).toInt ∧
    32768 * (BitVec.ofNat 16 (cen (zetaTable.getD k 0 * 3303 % 3329))).toInt -
      3329 * (BitVec.ofNat 16 (quo (zetaTable.getD k 0 * 3303 % 3329))).toInt ≤ 1664 := by
  decide +kernel

theorem isMulN {l : Nat} (i : Nat) (hl : l < 7) : IsMul (mulB l i) (mulT l i)
    (if l = 3 then if Low l i then (3303 : Zq) else 3303 * zk l i else zk l i) := by
  by_cases h : l = 3
  · subst h
    rw [ite_eq_left rfl]
    by_cases c : Low 3 i
    · rw [ite_eq_left c, mulB, mulT, mulN, ite_eq_left rfl, ite_eq_left c]
      exact ⟨by decide, by decide, by decide⟩
    · rw [ite_eq_right c, mulB, mulT, mulN, ite_eq_left rfl, ite_eq_right c]
      have hk : 128 >>> 3 - 1 - i / (2 * (2 <<< 3)) < 16 := by
        simp only [Nat.reduceShiftRight, Nat.reduceShiftLeft, Nat.reduceMul]; omega_using []
      obtain ⟨h1, h2, h3⟩ := scaled_facts _ hk
      refine ⟨?_, h2, h3⟩
      rw [val_mul_nat, ← zk_val hl, Nat.mul_comm (3303 : Zq).val]
      exact h1
  · rw [ite_eq_right h, mulB, mulT, mulN, ite_eq_right h, zk]
    have hk : 256 / (2 <<< l) - 1 - i / (2 * (2 <<< l)) < 128 ∧ 256 / (2 <<< l) = 128 >>> l := by
      match l, hl with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ =>
        simp only [Nat.reduceShiftRight, Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]; omega_using []
      | _ + 7, h => exact absurd h (by omega_using [])
    rw [← hk.2]
    exact isMul hk.1

theorem low_iff (l i : Nat) : Low l i ↔ i % (2 * (2 <<< l)) < 2 <<< l := Iff.rfl

/-- The lower input of a butterfly of which `i` is the upper. -/
theorem high_facts {l i : Nat} (h : i < 256) : i - 2 <<< l < 256 := by omega_using [h]

/-- The first three layers. -/
theorem rep_lo {F : Nat → BitVec 16} {P : Poly} (hF : ∀ i < 256, (F i).toNat = (P[i]!).val) :
    ∀ l ≤ 3, ∀ i < 256, Rep (iv F l i) (nttInvL l P)[i]! (loB l i) (hiB l i)
  | 0, _, i, hi => by
    have h := hF i hi
    have hl := val_lt_int (P[i]!)
    have := BitVec.toInt_eq_toNat_cond (F i)
    rw [ite_eq_left (by omega_using [h, hl])] at this
    have hb : loB 0 i = 0 ∧ hiB 0 i = 3328 := by
      have : i % 2 ^ (0 + 1) < 2 := Nat.mod_lt _ (by decide)
      simp only [loB, hiB, this, ↓reduceIte]; decide
    rw [hb.1, hb.2]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [iv, show nttInvL 0 P = P from rfl] <;> omega_using [this, h, hl]
  | l + 1, hl, i, hi => by
    have ih := rep_lo hF l (by omega_using [hl])
    have hl' : l < 7 := by omega_using [hl]
    have hb := bounds l (by omega_using [hl]) i hi
    rw [nttInvL_succ_get P hl' hi, iv, out, ite_eq_right (show ¬ l = 6 by omega_using [hl])]
    by_cases c : Low l i
    · rw [ite_eq_left c] at hb
      rw [ite_eq_left ⟨by omega_using [hl], c⟩, raw, ite_eq_left c, ite_eq_left ((low_iff l i).1 c), ofsN,
        ite_eq_right (fun hc => absurd hc.1 (by omega_using [hl])), show BitVec.ofNat 16 0 = 0#16 from rfl, BitVec.sub_zero]
      exact ((ih i hi).add (ih _ (lower_facts hl' c hi).1) hb.2.2.1 hb.2.2.2).mono hb.1 hb.2.1
    · rw [ite_eq_right c] at hb
      rw [ite_eq_right (fun hc => c hc.2), raw, ite_eq_right c, ite_eq_right (fun hc => c ((low_iff l i).2 hc))]
      have hm := isMulN i hl'
      rw [ite_eq_right (show ¬ l = 3 by omega_using [hl])] at hm
      exact (rep_red ((ih i hi).sub (ih _ (high_facts hi)) hb.2.2.1 hb.2.2.2).mod hm).mono hb.1 hb.2.1

/-- After the fourth layer, whose outputs are multiplied by 3303. -/
theorem rep_four {F : Nat → BitVec 16} {P : Poly} (hF : ∀ i < 256, (F i).toNat = (P[i]!).val) (i : Nat) (hi : i < 256) :
    Rep (iv F 4 i) (3303 * (nttInvL 4 P)[i]!) (-3328) 3328 := by
  have ih := rep_lo hF 3 (by decide)
  have hb := bounds3 i hi
  rw [nttInvL_succ_get P (j := 3) (by decide) hi, iv, out, ite_eq_right (by decide), ite_eq_right (fun h => h.1 rfl)]
  have hm := isMulN (l := 3) i (by decide)
  rw [ite_eq_left rfl] at hm
  by_cases c : Low 3 i
  · rw [ite_eq_left c] at hb hm
    rw [raw, ite_eq_left c, ite_eq_left ((low_iff 3 i).1 c)]
    refine rep_red (Rep.mod (lo := loB 3 i + loB 3 (i + 2 <<< 3) - ofsN 3 i) (hi := hiB 3 i + hiB 3 (i + 2 <<< 3) - ofsN 3 i) ?_) hm
    by_cases ho : i % 16 < 2
    · have e : ofsN 3 i = 26632 := by rw [ofsN, ite_eq_left ⟨rfl, ho⟩]
      rw [e] at hb ⊢
      exact (ih i hi).addOfs (ih _ (lower_facts (by decide) c hi).1) hb.1 hb.2
    · have e : ofsN 3 i = 0 := by rw [ofsN, ite_eq_right (fun hc => ho hc.2)]
      rw [e, Int.natCast_zero, Int.sub_zero, Int.sub_zero] at hb
      rw [e, Int.natCast_zero, Int.sub_zero, Int.sub_zero, show BitVec.ofNat 16 0 = 0#16 from rfl, BitVec.sub_zero]
      exact (ih i hi).add (ih _ (lower_facts (by decide) c hi).1) hb.1 hb.2
  · rw [ite_eq_right c] at hb hm
    rw [raw, ite_eq_right c, ite_eq_right (fun hc => c ((low_iff 3 i).2 hc)), ← mul_assoc_zq]
    exact rep_red ((ih i hi).sub (ih _ (high_facts hi)) hb.1 hb.2).mod hm

/-- The fifth and sixth layers. -/
theorem rep_hi {F : Nat → BitVec 16} {P : Poly} (hF : ∀ i < 256, (F i).toNat = (P[i]!).val) :
    ∀ k ≤ 2, ∀ i < 256, Rep (iv F (4 + k) i) (3303 * (nttInvL (4 + k) P)[i]!) (-(3328 * 2 ^ k)) (3328 * 2 ^ k)
  | 0, _, i, hi => by
    have := rep_four hF i hi
    rw [show (3328 * 2 ^ 0 : Int) = 3328 from rfl, Nat.add_zero]
    exact this
  | k + 1, hk, i, hi => by
    have ih := rep_hi hF k (by omega_using [hk])
    have hl : 4 + k < 7 := by omega_using [hk]
    have hb : (3328 * 2 ^ k : Int) + 3328 * 2 ^ k = 3328 * 2 ^ (k + 1) ∧ (3328 : Int) ≤ 3328 * 2 ^ (k + 1) ∧
        (3328 * 2 ^ (k + 1) : Int) < 32768 := by
      match k, hk with
      | 0, _ | 1, _ => decide
      | _ + 2, h => exact absurd h (by omega_using [])
    rw [show 4 + (k + 1) = 4 + k + 1 from rfl, nttInvL_succ_get P hl hi, iv, out,
      ite_eq_right (show ¬ 4 + k = 6 by omega_using [hk])]
    by_cases c : Low (4 + k) i
    · rw [ite_eq_left ⟨by omega_using [], c⟩, raw, ite_eq_left c, ite_eq_left ((low_iff _ i).1 c), ofsN,
        ite_eq_right (fun hc => absurd hc.1 (by omega_using [])), show BitVec.ofNat 16 0 = 0#16 from rfl, BitVec.sub_zero,
        mul_add_zq]
      exact ((ih i hi).add (ih _ (lower_facts hl c hi).1) (by omega_using [hb]) (by omega_using [hb])).mono
        (by omega_using [hb]) (by omega_using [hb])
    · rw [ite_eq_right (fun hc => c hc.2), raw, ite_eq_right c, ite_eq_right (fun hc => c ((low_iff _ i).2 hc)),
        ← mul_assoc_zq, mul_comm_zq 3303, mul_assoc_zq, mul_sub_zq]
      have hm := isMulN i hl
      rw [ite_eq_right (show ¬ 4 + k = 3 by omega_using [])] at hm
      exact (rep_red ((ih i hi).sub (ih _ (high_facts hi)) (by omega_using [hb]) (by omega_using [hb])).mod hm).mono
        (by omega_using [hb]) (by omega_using [hb])

/-- The values that the code leaves are the coefficients of the inverse NTT. -/
theorem value_final {F : Nat → BitVec 16} {P : Poly} (hF : ∀ i < 256, (F i).toNat = (P[i]!).val) {i : Nat}
    (hi : i < 256) : (value F (3584 + i)).toNat = ((Spec.MlKem.nttInv P)[i]!).val := by
  have ih : ∀ i < 256, Rep (iv F 6 i) (3303 * (nttInvL 6 P)[i]!) (-13312) 13312 := fun i hi =>
    (rep_hi hF 2 (by decide) i hi).mono (by decide) (by decide)
  rw [value, ite_eq_left (by omega_using [hi]), show (3584 + i) / 512 = 7 by omega_using [hi],
    show (3584 + i) % 256 = i by omega_using [hi], nttInv_eq_nttInvL, map_mul_get _ hi, mul_comm_zq,
    nttInvL_succ_get P (j := 6) (by decide) hi, iv, out, ite_eq_left rfl]
  by_cases c : Low 6 i
  · rw [ite_eq_left c, raw, ite_eq_left c, ite_eq_left ((low_iff 6 i).1 c), ofsN,
      ite_eq_right (fun hc => absurd hc.1 (by decide)), show BitVec.ofNat 16 0 = 0#16 from rfl, BitVec.sub_zero, mul_add_zq]
    exact canon_toNat ((ih i hi).add (ih _ (lower_facts (by decide) c hi).1) (by decide) (by decide)) (by decide) (by decide)
  · rw [ite_eq_right c, raw, ite_eq_right c, ite_eq_right (fun hc => c ((low_iff 6 i).2 hc)),
      ← mul_assoc_zq, mul_comm_zq 3303, mul_assoc_zq, mul_sub_zq]
    have hm := isMulN (l := 6) i (by decide)
    rw [ite_eq_right (show ¬ 6 = 3 by decide)] at hm
    exact pos_toNat (rep_red ((ih i hi).sub (ih _ (high_facts hi)) (by decide) (by decide)).mod hm)

end VG.Proof.MlKem.AArch64.Ntt16.Inverse
