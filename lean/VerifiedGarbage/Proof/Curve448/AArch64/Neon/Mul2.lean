module

public import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Value
public import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Convert
public import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Prep
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Macs
public import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Exec
import Mathlib.Algebra.BigOperators.Group.List.Basic
public import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Math
public import VerifiedGarbage.Impl.Curve448.AArch64.Neon
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Arith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! ### `Curve448.AArch64.Neon.Folds`, which only this module used -/

section

/-!
# Combining the halves' coefficients

Untrusted: everything here is checked by Lean. `foldS` turns the coefficients
`S_q` into `S_d - S_{d+8}` (in `v_d`) and `-S_d` (in `v_{d+8}`); `foldU` adds
`U_{d+8}` (in `v_{16+d}`) to both.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon

/-- Lane `e` of vector register `r` is `f r e`, modulo 2⁶⁴. -/
abbrev LaneEq (t : State) (r : Nat) (x : Nat → Int) : Prop := ∀ e < 2, lane (t.v (V r)) e % M64 = x e % M64

def foldSChunk (d : Nat) : List Instr :=
  [vo (.mov (V 28) (V (d + 8))), vo (.sub .d2 (V (d + 8)) (V 31) (V d)), vo (.sub .d2 (V d) (V d) (V 28))]

theorem foldS_eq : foldS = (List.range 7).flatMap foldSChunk ++ [vo (.sub .d2 (V 15) (V 31) (V 7))] := rfl

theorem cong_sub {x y a b : Int} (hx : x % M64 = a % M64) (hy : y % M64 = b % M64) :
    (x - y) % M64 = (a - b) % M64 := by rw [Int.sub_emod, hx, hy, ← Int.sub_emod]

theorem cong_add {x y a b : Int} (hx : x % M64 = a % M64) (hy : y % M64 = b % M64) :
    (x + y) % M64 = (a + b) % M64 := by rw [Int.add_emod, hx, hy, ← Int.add_emod]

theorem cong_neg {x a : Int} (hx : x % M64 = a % M64) : (0 - x) % M64 = (-a) % M64 := by
  rw [cong_sub (x := 0) (a := 0) rfl hx, Int.zero_sub]

theorem lane_zero (e : Nat) : lane (0 : BitVec 128) e = 0 := by simp [lane, vdword]

theorem foldSChunk_ok {s : State} {d : Nat} (hd : d < 7) {a b : Nat → Int} (ha : LaneEq s d a)
    (hb : LaneEq s (d + 8) b) (h31 : s.v (V 31) = 0) :
    WP isa (.block (foldSChunk d)) s fun t =>
      LaneEq t d (fun e => a e - b e) ∧ LaneEq t (d + 8) (fun e => - a e) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, r ≠ V 28 → r ≠ V d → r ≠ V (d + 8) → t.v r = s.v r) := by
  have n1 : V 28 ≠ V d := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  have n2 : V 28 ≠ V (d + 8) := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  have n3 : V (d + 8) ≠ V d := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  have n4 : V 31 ≠ V 28 := by decide
  have n5 : V 31 ≠ V (d + 8) := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  have n6 : V d ≠ V 28 := n1.symm
  have n7 : V d ≠ V (d + 8) := n3.symm
  have n8 : V (d + 8) ≠ V 28 := n2.symm
  have n9 : V 28 ≠ V 31 := n4.symm
  simp only [foldSChunk]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_nil_iff.mpr ⟨fun e he => ?_, fun e he => ?_, rfl, rfl, rfl, rfl, fun r h1 h2 h3 => ?_⟩
  · rw [RegUpd.v_setV_self, lane_sub _ _ he]
    exact cong_sub (ha e he) (hb e he)
  · rw [RegUpd.v_setV_of_ne _ _ n3, RegUpd.v_setV_self, lane_sub _ _ he, h31, lane_zero]
    exact cong_neg (ha e he)
  · rw [RegUpd.v_setV_of_ne _ _ h2, RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ h1]

theorem foldS_ok {s : State} (x : Nat → Nat → Int) (hx : ∀ q < 15, LaneEq s q (x q)) (h31 : s.v (V 31) = 0) :
    WP isa (.block foldS) s fun t =>
      (∀ d < 8, LaneEq t d (fun e => x d e - (if d < 7 then x (d + 8) e else 0))) ∧
      (∀ d < 8, LaneEq t (d + 8) (fun e => - x d e)) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ r : VReg, (∀ n < 16, r ≠ V n) → r ≠ V 28 → t.v r = s.v r) := by
  rw [foldS_eq, WP.block_append_iff]
  let inv := fun n (t : State) =>
    (∀ d < 7, LaneEq t d (fun e => x d e - (if d < n then x (d + 8) e else 0))) ∧
    (∀ d < 7, LaneEq t (d + 8) (fun e => if d < n then - x d e else x (d + 8) e)) ∧
    LaneEq t 7 (x 7) ∧ t.v (V 31) = 0 ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, (∀ n < 16, r ≠ V n) → r ≠ V 28 → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv (fun n t hn ⟨ta, tb, t7, t31, tm, tg, tr, tw, tv⟩ => ?_)
    7 (by decide) s ⟨fun d hd e he => by simp [hx d (by omega_arith) e he], fun d hd e he => by simp [hx (d + 8) (by omega_arith) e he],
      hx 7 (by decide), h31, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun t ⟨ta, tb, t7, t31, tm, tg, tr, tw, tv⟩ => ?_
  · refine WP.mono (foldSChunk_ok hn (ta n hn) (tb n hn) t31) fun u ⟨ua, ub, um, ug, ur, uw, uv⟩ =>
      ⟨fun d hd e he => ?_, fun d hd e he => ?_, ?_, ?_, um.trans tm, ug.trans tg, ur.trans tr, uw.trans tw,
        fun r h1 h2 => (uv r h2 (h1 n (by omega_arith)) (h1 (n + 8) (by omega_arith))).trans (tv r h1 h2)⟩
    · rcases (show d = n ∨ d ≠ n by omega_arith) with rfl | hne
      · rw [ua e he]; simp
      · rw [uv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) hne)
          (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), ta d hd e he]
        simp only [show (d < n + 1) = (d < n) from propext (by omega_arith)]
    · rcases (show d = n ∨ d ≠ n by omega_arith) with rfl | hne
      · rw [ub e he]; simp
      · rw [uv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
          (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), tb d hd e he]
        simp only [show (d < n + 1) = (d < n) from propext (by omega_arith)]
    · intro e he
      rw [uv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
        (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), t7 e he]
    · rw [uv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
        (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), t31]
  · refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr
      ⟨fun d hd e he => ?_, fun d hd e he => ?_, tm, tg, tr, tw, fun r h1 h2 => ?_⟩⟩
    · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))]
      rcases (show d < 7 ∨ d = 7 by omega_arith) with h | rfl
      · rw [ta d h e he]
      · rw [t7 e he]; simp
    · rcases (show d < 7 ∨ d = 7 by omega_arith) with h | rfl
      · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), tb d h e he]; simp [h]
      · rw [RegUpd.v_setV_self, lane_sub _ _ he, t31, lane_zero]
        exact cong_neg (t7 e he)
    · rw [RegUpd.v_setV_of_ne _ _ (h1 15 (by decide)), tv r h1 h2]

/-- After `U`: `U_{d+8}`, in `v_{16+d}`, into `v_d` and `v_{d+8}`. -/
def foldUChunk (d : Nat) : List Instr :=
  [vo (.add .d2 (V d) (V d) (V (16 + d))), vo (.add .d2 (V (d + 8)) (V (d + 8)) (V (16 + d)))]

theorem foldU_eq : foldU = (List.range 7).flatMap foldUChunk := rfl

theorem foldU_ok {s : State} (x y : Nat → Nat → Int) (hx : ∀ k < 16, LaneEq s k (x k))
    (hy : ∀ d < 7, LaneEq s (16 + d) (y d)) :
    WP isa (.block foldU) s fun t =>
      (∀ k < 16, LaneEq t k (fun e => x k e + (if k < 7 then y k e else if 8 ≤ k ∧ k < 15 then y (k - 8) e else 0))) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, (∀ n < 16, r ≠ V n) → t.v r = s.v r) := by
  rw [foldU_eq]
  let inv := fun n (t : State) =>
    (∀ k < 16, LaneEq t k (fun e => x k e + (if k < n then y k e else if 8 ≤ k ∧ k < 8 + n then y (k - 8) e else 0))) ∧
    (∀ d < 7, LaneEq t (16 + d) (y d)) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r : VReg, (∀ n < 16, r ≠ V n) → t.v r = s.v r)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv (fun n t hn ⟨ta, ty, tm, tg, tr, tw, tv⟩ => ?_)
    7 (by decide) s ⟨fun k hk e he => by simp [hx k hk e he, show ¬ (8 ≤ k ∧ k < 8) by omega_arith], hy, rfl, rfl, rfl,
      rfl, fun _ _ => rfl⟩)
    fun t ⟨ta, _, tm, tg, tr, tw, tv⟩ => ⟨fun k hk e he => by rw [ta k hk e he], tm, tg, tr, tw, tv⟩
  simp only [foldUChunk]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr
    ⟨fun k hk e he => ?_, fun d hd e he => ?_, tm, tg, tr, tw, fun r h1 => ?_⟩⟩
  · have hn8 : V (n + 8) ≠ V n := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
    have hU8 : V (16 + n) ≠ V n := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
    rcases (show k = n + 8 ∨ k = n ∨ (k ≠ n ∧ k ≠ n + 8) by omega_arith) with rfl | rfl | ⟨k1, k2⟩
    · rw [RegUpd.v_setV_self, lane_add _ _ he, RegUpd.v_setV_of_ne _ _ hn8,
        RegUpd.v_setV_of_ne _ _ hU8]
      rw [cong_add (ta _ hk e he) (ty n hn e he)]
      congr 1
      by_cases h : n + 8 < n <;> simp [h] <;> split <;> omega_arith
    · rw [RegUpd.v_setV_of_ne _ _ hn8.symm, RegUpd.v_setV_self, lane_add _ _ he,
        cong_add (ta _ hk e he) (ty k hn e he)]
      congr 1
      simp only [show k < k + 1 from by omega_arith, ite_true, show ¬ k < k from by omega_arith, ite_false]
      split <;> omega_arith
    · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega_arith) _ (by omega_arith) k2),
        RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega_arith) _ (by omega_arith) k1), ta k hk e he]
      congr 2
      by_cases h1 : k < n <;> by_cases h2 : k < n + 1 <;> by_cases h3 : 8 ≤ k ∧ k < 8 + n <;>
        by_cases h4 : 8 ≤ k ∧ k < 8 + (n + 1) <;> simp [h1, h2, h3, h4] <;> omega_arith
  · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)),
      RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), ty d hd e he]
  · rw [RegUpd.v_setV_of_ne _ _ (h1 _ (by omega_arith)), RegUpd.v_setV_of_ne _ _ (h1 _ (by omega_arith)), tv r h1]

end VG.Proof.Curve448.AArch64.Neon

end

end

/-! ### `Curve448.AArch64.Neon.Halves`, which only this module used -/

section

/-! ### `Curve448.AArch64.Neon.Pairs`, which only this module used -/

section

/-!
# Which limbs each product multiplies

Untrusted: everything here is checked by Lean. Product `p` of a half multiplies
half-limb `ia p` of the first operand by half-limb `ib p` of the second, at
coefficient `ia p + ib p`; the products at coefficient `q` are, up to order,
the terms of `cv x y q` (`perm_q`, by evaluation).
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Neon

open VG.Impl.Curve448.AArch64.Neon

def ia (p : Prod) : Nat := 2 * p.i + (if p.hi then 1 else 0)
def ib (p : Prod) : Nat :=
  if p.bv < 4 then 2 * p.bv + (if p.hi then 1 else 0) else 2 * (p.bv - 4) + (if p.hi then 1 else 0) - 1

/-- The terms `(i, q - i)` of coefficient `q`. -/
def pairsQ (q : Nat) : List (Nat × Nat) :=
  ((List.range 8).filter fun i => i ≤ q ∧ q - i < 8).map fun i => (i, q - i)

theorem prods_pos : ∀ p ∈ prods, p.pos = ia p + ib p ∧ ia p < 8 ∧ ib p < 8 ∧
    (p.bv ≥ 4 → (p.hi = false → p.bv ≠ 4) ∧ (p.hi = true → p.bv ≠ 8)) := by decide

theorem perm_q : ∀ q < 15, List.Perm ((prods.filter fun p => p.pos == q).map fun p => (ia p, ib p)) (pairsQ q) := by
  decide

theorem cv_pairs (x y : Nat → Nat) : ∀ q < 15, cv x y q = ((pairsQ q).map fun ij => x ij.1 * y ij.2).sum := by
  intro q hq
  rcases q with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | q
  all_goals first | omega | (simp [cv, pairsQ, List.range, List.range.loop]; try ring_nf)

end VG.Proof.Curve448.AArch64.Neon

end

end

/-!
# A half's products are its coefficients

Untrusted: everything here is checked by Lean. With the first operand's half
in vectors at `aHalf h` and the second's (and its shifted copy) at `bOff h`,
lane `e` of the products aimed at a register is coefficient `q` of the product
of the halves, `cv`.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off)

/-- The memory words of a half: element `c % 2`'s half-limb `2i + c / 2` in word `c` of vector `i`,
and the shifted copy of the second operand. -/
structure HalfMem (m : Mem) (base : Addr) (h : Nat) (X Y : Nat → Nat → Nat) : Prop where
  a : ∀ i < 4, ∀ c < 4, nw m base (aHalf h + 16 * i + 4 * c) = X (c % 2) (2 * i + c / 2)
  b : ∀ j < 4, ∀ c < 4, nw m base (bHalf h + 16 * j + 4 * c) = Y (c % 2) (2 * j + c / 2)
  sh : ∀ j < 5, ∀ c < 4, nw m base (NBP + 80 * h + 16 * j + 4 * c) =
    if c < 2 then (if j = 0 then 0 else Y (c % 2) (2 * j - 1)) else (if j = 4 then 0 else Y (c % 2) (2 * j))

theorem prodVal_eq {m : Mem} {base : Addr} {h : Nat} {X Y : Nat → Nat → Nat} (hm : HalfMem m base h X Y)
    {p : Prod} (hpm : p ∈ prods) {e : Nat} (he : e < 2) :
    prodVal (fun i => m.read (off base (aHalf h + 16 * i)) 16) (fun bv => m.read (off base (bOff h bv)) 16) p e =
      X e (ia p) * Y e (ib p) := by
  obtain ⟨-, -, -, hz⟩ := prods_pos p hpm
  obtain ⟨pi, pb⟩ := prods_facts p hpm
  have hc : hp p.hi + e < 4 := by unfold hp; split <;> omega_using [he]
  simp only [prodVal]
  rw [vword_ld _ _ _ hc, vword_ld _ _ _ hc, hm.a _ pi _ hc]
  have e1 : (hp p.hi + e) % 2 = e := by unfold hp; split <;> omega_using [he]
  have e2 : (hp p.hi + e) / 2 = if p.hi then 1 else 0 := by unfold hp; split <;> omega_using [he]
  rw [e1, e2]
  congr 1
  unfold bOff ib
  split
  · rename_i hb; rw [hm.b _ hb _ hc, e1, e2]
  · rename_i hb
    rw [show NBP + 80 * h + 16 * (p.bv - 4) + 4 * (hp p.hi + e) = NBP + 80 * h + 16 * (p.bv - 4) + 4 * (hp p.hi + e)
      from rfl, hm.sh _ (by omega_using [pb]) _ hc, e1]
    cases hhi : p.hi
    · have := (hz (by omega_using [hb])).1 hhi
      simp only [hp, Bool.false_eq_true, ite_false, Nat.zero_add, Nat.add_zero, show e < 2 from he, ite_true,
        show p.bv - 4 ≠ 0 by omega_using [hb, this]]
    · have := (hz (by omega_using [hb])).2 hhi
      simp only [hp, ite_true, show ¬ (2 + e < 2) by omega_using [], ite_false, show p.bv - 4 ≠ 4 by omega_using [this],
        Nat.add_sub_cancel]

theorem cast_sum {α : Type} (l : List α) (f : α → Nat) :
    (((l.map f).sum : Nat) : Int) = (l.map fun x => (f x : Int)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.sum_cons, ih]

theorem prodSum_cv {m : Mem} {base : Addr} {h : Nat} {X Y : Nat → Nat → Nat} (hm : HalfMem m base h X Y)
    {tgt : Nat → Nat} {r q : Nat} (hq : q < 15) (ht : ∀ p ∈ prods, tgt p.pos = r ↔ p.pos = q) {e : Nat} (he : e < 2) :
    prodSum (fun i => m.read (off base (aHalf h + 16 * i)) 16) (fun bv => m.read (off base (bOff h bv)) 16)
      tgt prods r e = cv (X e) (Y e) q := by
  simp only [prodSum]
  rw [List.filter_congr (q := fun p => p.pos == q) fun p hp => by simp [ht p hp],
    List.map_congr_left (g := fun p => ((X e (ia p) * Y e (ib p) : Nat) : Int)) fun p hp => by
      rw [prodVal_eq hm (List.mem_filter.mp hp).1 he],
    cv_pairs _ _ q hq]
  have hperm := (perm_q q hq).map (fun ij : Nat × Nat => ((X e ij.1 * Y e ij.2 : Nat) : Int))
  rw [List.map_map] at hperm
  rw [show (fun p => ((X e (ia p) * Y e (ib p) : Nat) : Int)) =
    (fun ij : Nat × Nat => ((X e ij.1 * Y e ij.2 : Nat) : Int)) ∘ (fun p => (ia p, ib p)) from rfl, hperm.sum_eq]
  rw [cast_sum]

end VG.Proof.Curve448.AArch64.Neon

end

end

/-!
# Two field multiplications in AdvSIMD

Untrusted: everything here is checked by Lean. `mul2 o₁ a₁ b₁ o₂ a₂ b₂`
writes products of `[a₁]` and `[b₁]`, and of `[a₂]` and `[b₂]`, to `o₁` and
`o₂`, with limbs below `Mb`, for operand limbs below `Ib`.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside Outside2 word limbs)
open VG.Proof.X448.Wide (valN valN_congr)
open VG.Proof.X448 (toFe)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

/-- The two elements' operands, as functions of the element. -/
abbrev pick (f₁ f₂ : Nat → Nat) (e : Nat) : Nat → Nat := if e = 0 then f₁ else f₂

theorem split_l28 (f₁ f₂ : Nat → Nat) (i c : Nat) (hc : c < 4) :
    split f₁ f₂ i c = l28 (pick f₁ f₂ (c % 2)) (2 * i + c / 2) := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega_arith) with rfl | rfl | rfl | rfl <;>
    simp [split, l28, pick, show (2 * i + 1) % 2 = 1 by omega_arith, show (2 * i + 1) / 2 = i by omega_arith]

theorem l28_lt {f : Nat → Nat} (hf : ∀ i < 8, f i < Ib) {k : Nat} (hk : k < 16) : l28 f k ≤ lmax k := by
  unfold l28 lmax
  split
  · have := Nat.mod_lt (f (k / 2)) (show 2 ^ 28 > 0 by decide); omega_arith
  · have := hf (k / 2) (by omega_arith)
    simp only [Ib] at this
    rw [Nat.div_le_iff_le_mul_add_pred (by decide)]
    omega_arith

/-- The preparation: constants, the radix-2²⁸ vectors, their sums and the shifted copies. -/
def prep (a₁ b₁ a₂ b₂ : Nat) : List Instr :=
  consts ++ convert a₁ a₂ NA 0 1 2 3 ++ convert b₁ b₂ NB 4 5 6 7 ++ sums ++ shifted

theorem lmax_le (k : Nat) : lmax k ≤ 3 * 2 ^ 28 := by unfold lmax; split <;> omega_arith

/-- The words of the operands after the preparation, as `HalfMem` wants them. -/
theorem halfMem_of {m : Mem} {base : Addr} {LA LB : Nat → Nat → Nat}
    (hla : ∀ e < 2, ∀ k < 16, LA e k ≤ lmax k) (hlb : ∀ e < 2, ∀ k < 16, LB e k ≤ lmax k)
    (hA : ∀ i < 8, ∀ c < 4, nw m base (NA + 16 * i + 4 * c) = LA (c % 2) (2 * i + c / 2))
    (hB : ∀ i < 8, ∀ c < 4, nw m base (NB + 16 * i + 4 * c) = LB (c % 2) (2 * i + c / 2))
    (hAS : ∀ i < 4, ∀ c < 4, nw m base (NAS + 16 * i + 4 * c) =
      (LA (c % 2) (2 * i + c / 2) + LA (c % 2) (8 + (2 * i + c / 2))) % 2 ^ 32)
    (hBS : ∀ i < 4, ∀ c < 4, nw m base (NBS + 16 * i + 4 * c) =
      (LB (c % 2) (2 * i + c / 2) + LB (c % 2) (8 + (2 * i + c / 2))) % 2 ^ 32)
    (hSh : ∀ h < 3, ∀ j < 5, ∀ c < 4, nw m base (NBP + 80 * h + 16 * j + 4 * c) =
      if c < 2 then (if j = 0 then 0 else hl (LB (c % 2)) h (2 * j - 1)) else (if j = 4 then 0 else hl (LB (c % 2)) h (2 * j)))
    {h : Nat} (hh : h < 3) :
    HalfMem m base h (fun e => hl (LA e) h) (fun e => hl (LB e) h) := by
  have hNA : NA = 4096 := rfl
  have hNB : NB = 4224 := rfl
  have hNAS : NAS = 4352 := rfl
  have hNBS : NBS = 4416 := rfl
  refine ⟨fun i hi c hc => ?_, fun j hj c hc => ?_, fun j hj c hc => hSh h hh j hj c hc⟩
  · rcases (show h = 0 ∨ h = 1 ∨ h = 2 by omega_arith) with rfl | rfl | rfl
    · simp only [aHalf, hl]; exact hA i (by omega_arith) c hc
    · simp only [aHalf, hl]
      rw [show NA + 64 + 16 * i + 4 * c = NA + 16 * (i + 4) + 4 * c by omega_arith, hA (i + 4) (by omega_arith) c hc]
      congr 1; omega_arith
    · simp only [aHalf, hl]
      rw [hAS i hi c hc, Nat.mod_eq_of_lt]
      have := hla (c % 2) (by omega_arith) (2 * i + c / 2) (by omega_arith)
      have := hla (c % 2) (by omega_arith) (8 + (2 * i + c / 2)) (by omega_arith)
      have := lmax_le (2 * i + c / 2); have := lmax_le (8 + (2 * i + c / 2))
      omega_arith
  · rcases (show h = 0 ∨ h = 1 ∨ h = 2 by omega_arith) with rfl | rfl | rfl
    · simp only [bHalf, hl]; exact hB j (by omega_arith) c hc
    · simp only [bHalf, hl]
      rw [show NB + 64 + 16 * j + 4 * c = NB + 16 * (j + 4) + 4 * c by omega_arith, hB (j + 4) (by omega_arith) c hc]
      congr 1; omega_arith
    · simp only [bHalf, hl]
      rw [hBS j hj c hc, Nat.mod_eq_of_lt]
      have := hlb (c % 2) (by omega_arith) (2 * j + c / 2) (by omega_arith)
      have := hlb (c % 2) (by omega_arith) (8 + (2 * j + c / 2)) (by omega_arith)
      have := lmax_le (2 * j + c / 2); have := lmax_le (8 + (2 * j + c / 2))
      omega_arith

theorem halfB_of {m : Mem} {base : Addr} {LB : Nat → Nat → Nat} (hlb : ∀ e < 2, ∀ k < 16, LB e k ≤ lmax k)
    (hB : ∀ i < 8, ∀ c < 4, nw m base (NB + 16 * i + 4 * c) = LB (c % 2) (2 * i + c / 2))
    (hBS : ∀ i < 4, ∀ c < 4, nw m base (NBS + 16 * i + 4 * c) =
      (LB (c % 2) (2 * i + c / 2) + LB (c % 2) (8 + (2 * i + c / 2))) % 2 ^ 32) :
    ∀ h < 3, ∀ j < 4, ∀ c < 4, nw m base (bHalf h + 16 * j + 4 * c) = hl (LB (c % 2)) h (2 * j + c / 2) := by
  have hNB : NB = 4224 := rfl
  have hNBS : NBS = 4416 := rfl
  intro h hh j hj c hc
  rcases (show h = 0 ∨ h = 1 ∨ h = 2 by omega_arith) with rfl | rfl | rfl
  · simp only [bHalf, hl]; exact hB j (by omega_arith) c hc
  · simp only [bHalf, hl]
    rw [show NB + 64 + 16 * j + 4 * c = NB + 16 * (j + 4) + 4 * c by omega_arith, hB (j + 4) (by omega_arith) c hc]
    congr 1; omega_arith
  · simp only [bHalf, hl]
    rw [hBS j hj c hc, Nat.mod_eq_of_lt]
    have := hlb (c % 2) (by omega_arith) (2 * j + c / 2) (by omega_arith)
    have := hlb (c % 2) (by omega_arith) (8 + (2 * j + c / 2)) (by omega_arith)
    have := lmax_le (2 * j + c / 2); have := lmax_le (8 + (2 * j + c / 2))
    omega_arith

theorem sh_of {m : Mem} {base : Addr} {LB : Nat → Nat → Nat}
    (hb : ∀ h < 3, ∀ j < 4, ∀ c < 4, nw m base (bHalf h + 16 * j + 4 * c) = hl (LB (c % 2)) h (2 * j + c / 2)) :
    ∀ h < 3, ∀ j < 5, ∀ c < 4, shw (nw m base) h j c =
      if c < 2 then (if j = 0 then 0 else hl (LB (c % 2)) h (2 * j - 1)) else (if j = 4 then 0 else hl (LB (c % 2)) h (2 * j)) := by
  intro h hh j hj c hc
  unfold shw
  split
  · split
    · rfl
    · rw [hb h hh (j - 1) (by omega_arith) (c + 2) (by omega_arith), show (c + 2) % 2 = c % 2 by omega_arith]
      congr 1; omega_arith
  · split
    · rfl
    · rw [hb h hh j (by omega_arith) (c - 2) (by omega_arith), show (c - 2) % 2 = c % 2 by omega_arith]
      congr 1; omega_arith

/-- Element `e`'s radix-2²⁸ limbs of `[x₁]` (`e = 0`) or `[x₂]`. -/
abbrev L28 (m : Mem) (base : Addr) (x₁ x₂ : Nat) (e : Nat) : Nat → Nat :=
  l28 (pick (limbs m base x₁) (limbs m base x₂) e)

theorem L28_le {m : Mem} {base : Addr} {x₁ x₂ : Nat} (h₁ : ∀ i < 8, limbs m base x₁ i < Ib)
    (h₂ : ∀ i < 8, limbs m base x₂ i < Ib) : ∀ e < 2, ∀ k < 16, L28 m base x₁ x₂ e k ≤ lmax k := by
  intro e he k hk
  simp only [L28, pick]
  split
  · exact l28_lt h₁ hk
  · exact l28_lt h₂ hk

theorem L28_congr {m m' : Mem} {base : Addr} {x₁ x₂ : Nat} (h₁ : ∀ i < 8, limbs m' base x₁ i = limbs m base x₁ i)
    (h₂ : ∀ i < 8, limbs m' base x₂ i = limbs m base x₂ i) {e k : Nat} (hk : k < 16) :
    L28 m' base x₁ x₂ e k = L28 m base x₁ x₂ e k := by
  simp only [L28, l28, pick]
  split <;> split <;> simp only [h₁ (k / 2) (by omega_arith), h₂ (k / 2) (by omega_arith)]

theorem prep_ok {s : State} {base : Addr} (hs : Scr s base) {a₁ b₁ a₂ b₂ : Nat}
    (ha₁ : a₁ % 16 = 0 ∧ a₁ + 64 ≤ NA) (hb₁ : b₁ % 16 = 0 ∧ b₁ + 64 ≤ NA)
    (ha₂ : a₂ % 16 = 0 ∧ a₂ + 64 ≤ NA) (hb₂ : b₂ % 16 = 0 ∧ b₂ + 64 ≤ NA)
    (la₁ : ∀ i < 8, limbs s.mem base a₁ i < Ib) (lb₁ : ∀ i < 8, limbs s.mem base b₁ i < Ib)
    (la₂ : ∀ i < 8, limbs s.mem base a₂ i < Ib) (lb₂ : ∀ i < 8, limbs s.mem base b₂ i < Ib) :
    WP isa (.block (prep a₁ b₁ a₂ b₂)) s fun t =>
      (∀ h < 3, HalfMem t.mem base h (fun e => hl (L28 s.mem base a₁ a₂ e) h) (fun e => hl (L28 s.mem base b₁ b₂ e) h)) ∧
      (∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) ∧ t.v (V 31) = 0 ∧
      Outside base NA 640 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hNA : NA = 4096 := rfl
  have hNB : NB = 4224 := rfl
  have hNAS : NAS = 4352 := rfl
  have hNBS : NBS = 4416 := rfl
  have hNBP : NBP = 4480 := rfl
  have nn : ∀ a < 32, ∀ b < 32, a ≠ b → V a ≠ V b := V_ne
  obtain lt60 : ∀ x ∈ [a₁, b₁, a₂, b₂], ∀ i < 8, limbs s.mem base x i < Ib → limbs s.mem base x i < 2 ^ 60 :=
    fun _ _ _ _ h => by simp only [Ib] at h; omega_arith
  simp only [prep, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok hs) fun t1 ⟨hM, h31, m1, rd1, wr1, g1, v1, s1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (convert_ok s1 ha₁.1 (by omega_arith) ha₂.1 (by omega_arith) (by decide) (by decide) (Or.inl (by omega_arith))
    (Or.inl (by omega_arith)) hM (nn 0 (by decide) 1 (by decide) (by decide)) (nn 0 (by decide) 2 (by decide) (by decide))
    (nn 0 (by decide) 3 (by decide) (by decide)) (nn 1 (by decide) 2 (by decide) (by decide))
    (nn 1 (by decide) 3 (by decide) (by decide)) (nn 2 (by decide) 3 (by decide) (by decide))
    (fun r hr => nn r (by simp at hr; omega_arith) 30 (by decide) (by simp at hr; omega_arith))
    (fun i hi => by rw [m1]; exact lt60 a₁ (by simp) i hi (la₁ i hi))
    (fun i hi => by rw [m1]; exact lt60 a₂ (by simp) i hi (la₂ i hi)))
    fun t2 ⟨A2, o2, g2, r2, w2, v2⟩ => ?_
  obtain s2 : Scr t2 base := scr_of s1 g2 w2
  obtain M2 : ∀ e < 2, (vdword (t2.v (V 30)) e).toNat = 2 ^ 28 - 1 := fun e he => by
    rw [v2 _ (by decide)]; exact hM e he
  rw [WP.block_append_iff]
  refine WP.mono (convert_ok s2 hb₁.1 (by omega_arith) hb₂.1 (by omega_arith) (by decide) (by decide) (Or.inl (by omega_arith))
    (Or.inl (by omega_arith)) M2 (nn 4 (by decide) 5 (by decide) (by decide)) (nn 4 (by decide) 6 (by decide) (by decide))
    (nn 4 (by decide) 7 (by decide) (by decide)) (nn 5 (by decide) 6 (by decide) (by decide))
    (nn 5 (by decide) 7 (by decide) (by decide)) (nn 6 (by decide) 7 (by decide) (by decide))
    (fun r hr => nn r (by simp at hr; omega_arith) 30 (by decide) (by simp at hr; omega_arith))
    (fun i hi => by rw [VG.Proof.Curve448.AArch64.Neon.limbs_outside o2 (Or.inl (by omega_arith)) (by omega_arith) hi, m1]
                    exact lt60 b₁ (by simp) i hi (lb₁ i hi))
    (fun i hi => by rw [VG.Proof.Curve448.AArch64.Neon.limbs_outside o2 (Or.inl (by omega_arith)) (by omega_arith) hi, m1]
                    exact lt60 b₂ (by simp) i hi (lb₂ i hi)))
    fun t3 ⟨B3, o3, g3, r3, w3, v3⟩ => ?_
  obtain s3 : Scr t3 base := scr_of s2 g3 w3
  rw [WP.block_append_iff]
  refine WP.mono (sums_ok s3) fun t4 ⟨AS4, BS4, o4, g4, r4, w4, v4⟩ => ?_
  obtain s4 : Scr t4 base := scr_of s3 g4 w4
  obtain h31' : t4.v (V 31) = 0 := by rw [v4 _ (by decide), v3 _ (by decide), v2 _ (by decide)]; exact h31
  refine WP.mono (shifted_ok s4 h31') fun t5 ⟨Sh5, o5, g5, r5, w5, v5⟩ => ?_
  -- the words of the vectors
  obtain LAe : ∀ e < 2, ∀ k < 16, L28 s.mem base a₁ a₂ e k ≤ lmax k := L28_le la₁ la₂
  obtain LBe : ∀ e < 2, ∀ k < 16, L28 s.mem base b₁ b₂ e k ≤ lmax k := L28_le lb₁ lb₂
  obtain A2' : ∀ i < 8, ∀ c < 4, nw t2.mem base (NA + 16 * i + 4 * c) = L28 s.mem base a₁ a₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by rw [A2 i hi c hc, split_l28 _ _ _ _ hc, m1]
  obtain B3' : ∀ i < 8, ∀ c < 4, nw t3.mem base (NB + 16 * i + 4 * c) = L28 s.mem base b₁ b₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by
      rw [B3 i hi c hc, split_l28 _ _ _ _ hc]
      refine (L28_congr (m := s.mem) (fun i' hi' => ?_) (fun i' hi' => ?_) (by omega_arith))
      · rw [VG.Proof.Curve448.AArch64.Neon.limbs_outside o2 (Or.inl (by omega_arith)) (by omega_arith) hi', m1]
      · rw [VG.Proof.Curve448.AArch64.Neon.limbs_outside o2 (Or.inl (by omega_arith)) (by omega_arith) hi', m1]
  obtain A3 : ∀ i < 8, ∀ c < 4, nw t3.mem base (NA + 16 * i + 4 * c) = L28 s.mem base a₁ a₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by rw [Outside.nw o3 (by omega_arith) (by omega_arith)]; exact A2' i hi c hc
  obtain hA : ∀ i < 8, ∀ c < 4, nw t5.mem base (NA + 16 * i + 4 * c) = L28 s.mem base a₁ a₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by
      rw [Outside.nw o5 (by omega_arith) (by omega_arith), Outside.nw o4 (by omega_arith) (by omega_arith)]; exact A3 i hi c hc
  obtain B4 : ∀ i < 8, ∀ c < 4, nw t4.mem base (NB + 16 * i + 4 * c) = L28 s.mem base b₁ b₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by rw [Outside.nw o4 (by omega_arith) (by omega_arith)]; exact B3' i hi c hc
  obtain hB : ∀ i < 8, ∀ c < 4, nw t5.mem base (NB + 16 * i + 4 * c) = L28 s.mem base b₁ b₂ (c % 2) (2 * i + c / 2) :=
    fun i hi c hc => by rw [Outside.nw o5 (by omega_arith) (by omega_arith)]; exact B4 i hi c hc
  obtain AS : ∀ i < 4, ∀ c < 4, nw t4.mem base (NAS + 16 * i + 4 * c) =
      (L28 s.mem base a₁ a₂ (c % 2) (2 * i + c / 2) + L28 s.mem base a₁ a₂ (c % 2) (8 + (2 * i + c / 2))) % 2 ^ 32 :=
    fun i hi c hc => by
      rw [AS4 i hi c hc, A3 i (by omega_arith) c hc, A3 (i + 4) (by omega_arith) c hc, show 2 * (i + 4) + c / 2 = 8 + (2 * i + c / 2)
        by omega_arith]
  obtain BS : ∀ i < 4, ∀ c < 4, nw t4.mem base (NBS + 16 * i + 4 * c) =
      (L28 s.mem base b₁ b₂ (c % 2) (2 * i + c / 2) + L28 s.mem base b₁ b₂ (c % 2) (8 + (2 * i + c / 2))) % 2 ^ 32 :=
    fun i hi c hc => by
      rw [BS4 i hi c hc, B3' i (by omega_arith) c hc, B3' (i + 4) (by omega_arith) c hc, show 2 * (i + 4) + c / 2 = 8 + (2 * i + c / 2)
        by omega_arith]
  obtain hb4 := halfB_of LBe B4 BS
  obtain hSh : ∀ h < 3, ∀ j < 5, ∀ c < 4, nw t5.mem base (NBP + 80 * h + 16 * j + 4 * c) =
      if c < 2 then (if j = 0 then 0 else hl (L28 s.mem base b₁ b₂ (c % 2)) h (2 * j - 1))
      else (if j = 4 then 0 else hl (L28 s.mem base b₁ b₂ (c % 2)) h (2 * j)) :=
    fun h hh j hj c hc => by rw [Sh5 h hh j hj c hc, sh_of hb4 h hh j hj c hc]
  refine ⟨fun h hh => halfMem_of LAe LBe hA hB (fun i hi c hc => by
      rw [Outside.nw o5 (by omega_arith) (by omega_arith)]; exact AS i hi c hc)
    (fun i hi c hc => by rw [Outside.nw o5 (by omega_arith) (by omega_arith)]; exact BS i hi c hc) hSh hh,
    fun e he => by rw [v5 _ (by decide), v4 _ (by decide), v3 _ (by decide), v2 _ (by decide)]; exact hM e he,
    by rw [v5 _ (by decide), v4 _ (by decide), v3 _ (by decide), v2 _ (by decide)]; exact h31,
    ?_, by rw [g5, g4, g3, g2, g1], by rw [r5, r4, r3, r2, rd1], by rw [w5, w4, w3, w2, wr1]⟩
  rw [m1] at o2
  exact (((o2.mono (by omega_arith) (by omega_arith)).trans (o3.mono (by omega_arith) (by omega_arith))).trans
    (o4.mono (by omega_arith) (by omega_arith))).trans (o5.mono (by omega_arith) (by omega_arith))

/-- The target of `U`'s coefficients. -/
abbrev tgtU (p : Nat) : Nat := if p < 8 then p + 8 else 16 + (p - 8)

theorem prods_pos_lt : ∀ p ∈ prods, p.pos < 15 := by decide
theorem prods_hit : ∀ q < 15, ∃ p ∈ prods, p.pos = q := by decide

theorem half_offsets (h : Nat) (hh : h < 3) :
    (∀ i < 4, (aHalf h + 16 * i) % 16 = 0 ∧ aHalf h + 16 * i + 16 ≤ 8192) ∧
    (∀ bv < 9, bOff h bv % 16 = 0 ∧ bOff h bv + 16 ≤ 8192) := by
  rcases (show h = 0 ∨ h = 1 ∨ h = 2 by omega_arith) with rfl | rfl | rfl <;> decide

/-- A half's coefficient `q`, in register `tgt q`, from the `HalfMem` words. -/
theorem half_lanes {s : State} {base : Addr} (hs : Scr s base) {h : Nat} (hh : h < 3)
    {X Y : Nat → Nat → Nat} (hm : HalfMem s.mem base h X Y) (tgt : Nat → Nat) (fresh : List Nat)
    (ht : ∀ p ∈ prods, tgt p.pos < 23) (hinj : ∀ q < 15, ∀ q' < 15, tgt q = tgt q' → q = q') :
    WP isa (.block (half h tgt fresh)) s fun u =>
      u.mem = s.mem ∧ u.gpr = s.gpr ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      (∀ q < 15, ∀ e < 2, lane (u.v (V (tgt q))) e % M64 =
        ((if tgt q ∈ fresh then 0 else lane (s.v (V (tgt q))) e) + cv (X e) (Y e) q) % M64) ∧
      (∀ r : VReg, (∀ n ∈ [23, 24, 25, 26, 27], r ≠ V n) → (∀ q < 15, r ≠ V (tgt q)) → u.v r = s.v r) := by
  obtain ⟨ha, hoff⟩ := half_offsets h hh
  refine WP.mono (half_ok hs tgt fresh ht ha hoff) fun u ⟨um, ug, ur, uw, ua, uv⟩ =>
    ⟨um, ug, ur, uw, fun q hq e he => ?_, fun r h1 h2 => uv r h1 fun p hp => h2 p.pos (prods_pos_lt p hp)⟩
  obtain hp := prods_hit q hq
  rw [ua (tgt q) (by obtain ⟨p, pm, rfl⟩ := hp; exact ht p pm) (Or.inr (by
      obtain ⟨p, pm, e'⟩ := hp; exact ⟨p, pm, by rw [e']⟩)) e he,
    prodSum_cv hm hq (fun p pm => ⟨fun e' => hinj _ (prods_pos_lt p pm) _ hq e', fun e' => by rw [e']⟩) he]

/-- From the operands' halves to Karatsuba's coefficients. -/
def prodsCode : List Instr :=
  half 0 (fun p => p) (List.range 15) ++ foldS ++ half 1 (fun p => p) [] ++
    half 2 tgtU ((List.range 7).map (16 + ·)) ++ foldU

theorem tgtU_lo {q : Nat} (hq : q < 8) : tgtU q = q + 8 := ite_eq_left hq
theorem tgtU_hi {q : Nat} (hq : 8 ≤ q) : tgtU q = 16 + (q - 8) := ite_eq_right (by omega_arith)
theorem tgtU_inj : ∀ q < 15, ∀ q' < 15, tgtU q = tgtU q' → q = q' := by decide
theorem tgtU_lt : ∀ q < 15, tgtU q < 23 := by decide
theorem tgtU_fresh : ∀ k < 16, k ∉ (List.range 7).map (16 + ·) := by decide
theorem fresh_mem : ∀ d < 7, 16 + d ∈ (List.range 7).map (16 + ·) := by decide

theorem not_tmp {k : Nat} (hk : k < 23) : ∀ n ∈ [23, 24, 25, 26, 27], V k ≠ V n :=
  fun n hn => V_ne k (by omega_arith) n (by simp at hn; omega_arith) (by simp at hn; omega_arith)

theorem lane_step {s u : State} {r : Nat} {x c : Nat → Int} (hx : LaneEq s r x)
    (hu : ∀ e < 2, lane (u.v (V r)) e % M64 = (lane (s.v (V r)) e + c e) % M64) :
    LaneEq u r (fun e => x e + c e) := fun e he => (hu e he).trans (cong_add (hx e he) rfl)

theorem kara_fold (a b : Nat → Nat) {k : Nat} (hk : k < 16) :
    (if k < 8 then (S a b k : Int) - (if k < 7 then (S a b (k + 8) : Int) else 0) else -(S a b (k - 8) : Int)) +
      (if k < 15 then (T a b k : Int) else 0) + (if 8 ≤ k then (U a b (k - 8) : Int) else 0) +
      (if k < 7 then (U a b (k + 8) : Int) else if 8 ≤ k ∧ k < 15 then (U a b (k - 8 + 8) : Int) else 0) =
      kara a b k := by
  have s15 : S a b 15 = 0 := rfl
  have t15 : T a b 15 = 0 := rfl
  have u15 : U a b 15 = 0 := rfl
  rcases (by omega_arith : k < 7 ∨ k = 7 ∨ (8 ≤ k ∧ k < 15) ∨ k = 15) with h | rfl | h | rfl
  · simp (disch := omega_arith) only [kara, ite_eq_left, ite_eq_right]; omega_arith
  · simp only [kara, s15, u15]; simp
  · have e : k - 8 + 8 = k := by omega_arith
    simp (disch := omega_arith) only [kara, ite_eq_left, ite_eq_right, e]; omega_arith
  · simp only [kara, t15, u15]; simp; omega_arith

theorem prods_ok {s : State} {base : Addr} (hs : Scr s base) {X Y : Nat → Nat → Nat}
    (hm : ∀ h < 3, HalfMem s.mem base h (fun e => hl (X e) h) (fun e => hl (Y e) h)) (h31 : s.v (V 31) = 0) :
    WP isa (.block prodsCode) s fun t =>
      (∀ k < 16, LaneEq t k (fun e => kara (X e) (Y e) k)) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ r : VReg, (∀ n < 29, r ≠ V n) → t.v r = s.v r) := by
  simp only [prodsCode, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (half_lanes hs (by decide) (hm 0 (by decide)) (fun p => p) (List.range 15)
    (fun p hp => by have := prods_pos_lt p hp; omega_arith) (fun _ _ _ _ h => h)) fun t1 ⟨m1, g1, r1, w1, l1, v1⟩ => ?_
  obtain hx1 : ∀ q < 15, LaneEq t1 q (fun e => (S (X e) (Y e) q : Int)) := fun q hq e he => by
    rw [l1 q hq e he, ite_eq_left (List.mem_range.2 hq), Int.zero_add]
  obtain h31' : t1.v (V 31) = 0 := by
    rw [v1 _ (fun n hn => V_ne 31 (by decide) n (by simp at hn; omega_arith) (by simp at hn; omega_arith))
      (fun q hq => V_ne 31 (by decide) q (by omega_arith) (by omega_arith)), h31]
  rw [WP.block_append_iff]
  refine WP.mono (foldS_ok _ hx1 h31') fun t2 ⟨f1, f2, m2, g2, r2, w2, v2⟩ => ?_
  obtain hx2 : ∀ k < 16, LaneEq t2 k (fun e => if k < 8 then (S (X e) (Y e) k : Int) -
      (if k < 7 then (S (X e) (Y e) (k + 8) : Int) else 0) else -(S (X e) (Y e) (k - 8) : Int)) := fun k hk e he => by
    dsimp only
    by_cases h8 : k < 8
    · rw [ite_eq_left h8]; exact f1 k h8 e he
    · rw [ite_eq_right h8]; have := f2 (k - 8) (by omega_arith) e he; rwa [Nat.sub_add_cancel (by omega_arith)] at this
  obtain s2 : Scr t2 base := scr_of hs (g2.trans g1) (w2.trans w1)
  obtain hm2 : ∀ h < 3, HalfMem t2.mem base h (fun e => hl (X e) h) (fun e => hl (Y e) h) := by
    rw [m2, m1]; exact hm
  rw [WP.block_append_iff]
  refine WP.mono (half_lanes s2 (by decide) (hm2 1 (by decide)) (fun p => p) []
    (fun p hp => by have := prods_pos_lt p hp; omega_arith) (fun _ _ _ _ h => h)) fun t3 ⟨m3, g3, r3, w3, l3, v3⟩ => ?_
  obtain hx3 : ∀ k < 16, LaneEq t3 k (fun e => (if k < 8 then (S (X e) (Y e) k : Int) -
      (if k < 7 then (S (X e) (Y e) (k + 8) : Int) else 0) else -(S (X e) (Y e) (k - 8) : Int)) +
      (if k < 15 then (T (X e) (Y e) k : Int) else 0)) := fun k hk => by
    by_cases h15 : k < 15
    · refine lane_step (hx2 k hk) fun e he => ?_
      rw [l3 k h15 e he, ite_eq_right (List.not_mem_nil), ite_eq_left h15]
    · obtain rfl : k = 15 := by omega_arith
      intro e he
      dsimp only
      rw [v3 _ (not_tmp (by decide)) (fun q hq => V_ne 15 (by decide) q (by omega_arith) (by omega_arith)), ite_eq_right h15,
        Int.add_zero]
      exact hx2 15 hk e he
  obtain s3 : Scr t3 base := scr_of s2 g3 w3
  obtain hm3 : ∀ h < 3, HalfMem t3.mem base h (fun e => hl (X e) h) (fun e => hl (Y e) h) := by
    rw [m3]; exact hm2
  rw [WP.block_append_iff]
  refine WP.mono (half_lanes s3 (by decide) (hm3 2 (by decide)) tgtU _
    (fun p hp => tgtU_lt _ (prods_pos_lt p hp)) tgtU_inj) fun t4 ⟨m4, g4, r4, w4, l4, v4⟩ => ?_
  obtain hx4 : ∀ k < 16, LaneEq t4 k (fun e => ((if k < 8 then (S (X e) (Y e) k : Int) -
      (if k < 7 then (S (X e) (Y e) (k + 8) : Int) else 0) else -(S (X e) (Y e) (k - 8) : Int)) +
      (if k < 15 then (T (X e) (Y e) k : Int) else 0)) + (if 8 ≤ k then (U (X e) (Y e) (k - 8) : Int) else 0)) :=
      fun k hk => by
    by_cases h8 : 8 ≤ k
    · refine lane_step (hx3 k hk) fun e he => ?_
      have := l4 (k - 8) (by omega_arith) e he
      rw [tgtU_lo (by omega_arith), Nat.sub_add_cancel h8, ite_eq_right (tgtU_fresh k hk)] at this
      rw [this, ite_eq_left h8]
    · intro e he
      dsimp only
      rw [v4 _ (not_tmp (by omega_arith)) (fun q hq => V_ne k (by omega_arith) _ (by have := tgtU_lt q hq; omega_arith)
          (by unfold tgtU; split <;> omega_arith)), ite_eq_right h8, Int.add_zero]
      exact hx3 k hk e he
  obtain hy4 : ∀ d < 7, LaneEq t4 (16 + d) (fun e => (U (X e) (Y e) (d + 8) : Int)) := fun d hd e he => by
    have := l4 (d + 8) (by omega_arith) e he
    rw [tgtU_hi (by omega_arith), Nat.add_sub_cancel, ite_eq_left (fresh_mem d hd), Int.zero_add] at this
    exact this
  refine WP.mono (foldU_ok _ _ hx4 hy4) fun t5 ⟨l5, m5, g5, r5, w5, v5⟩ =>
    ⟨fun k hk e he => (l5 k hk e he).trans (by dsimp only; rw [kara_fold _ _ hk]), m5.trans (m4.trans (m3.trans (m2.trans m1))),
      g5.trans (g4.trans (g3.trans (g2.trans g1))), r5.trans (r4.trans (r3.trans (r2.trans r1))),
      w5.trans (w4.trans (w3.trans (w2.trans w1))), fun r hr => ?_⟩
  obtain tmp : ∀ n ∈ [23, 24, 25, 26, 27], r ≠ V n := fun n hn => hr n (by simp at hn; omega_arith)
  rw [v5 r (fun n hn => hr n (by omega_arith)), v4 r tmp (fun q hq => hr _ (by have := tgtU_lt q hq; omega_arith)),
    v3 r tmp (fun q hq => hr _ (by omega_arith)), v2 r (fun n hn => hr n (by omega_arith)) (hr 28 (by decide)),
    v1 r tmp (fun q hq => hr _ (by omega_arith))]

theorem mul2_eq (o₁ a₁ b₁ o₂ a₂ b₂ : Nat) :
    mul2 o₁ a₁ b₁ o₂ a₂ b₂ = prep a₁ b₁ a₂ b₂ ++ (prodsCode ++ (carries ++ finish o₁ o₂)) := by
  simp only [mul2, prep, prodsCode, List.append_assoc]

theorem toNat_lt {x : Int} (h : x < 2 ^ 64 - 2 ^ 40) : x.toNat < 2 ^ 64 - 2 ^ 40 := by omega_arith

theorem lane_exact {t : State} {k : Nat} {x : Int} (h0 : 0 ≤ x) (h1 : x < 2 ^ 64 - 2 ^ 40) {e : Nat}
    (h : lane (t.v (V k)) e % M64 = x % M64) : (vdword (t.v (V k)) e).toNat = x.toNat := by
  obtain hl := lane_lt (t.v (V k)) e
  rw [Int.emod_eq_of_lt (by simp [lane]) hl, Int.emod_eq_of_lt h0 (by simp only [M64]; omega_arith)] at h
  simp only [lane] at h; omega_arith

theorem limbs28_even {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) {i : Nat} (hi : i < 8) :
    limbs28 r (2 * i) < 2 ^ 40 := by
  have := limbs28_lt hr (show 2 * i < 16 by omega_arith)
  split at this <;> split at this <;> omega_arith

theorem limbs28_odd {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) {i : Nat} (hi : i < 8) :
    limbs28 r (2 * i + 1) < 2 ^ 28 := by
  have := limbs28_lt hr (show 2 * i + 1 < 16 by omega_arith)
  split at this <;> split at this <;> omega_arith

theorem mul2_ok {s : State} {base : Addr} (hs : Scr s base) {o₁ a₁ b₁ o₂ a₂ b₂ : Nat}
    (ha₁ : a₁ % 16 = 0 ∧ a₁ + 64 ≤ NA) (hb₁ : b₁ % 16 = 0 ∧ b₁ + 64 ≤ NA)
    (ha₂ : a₂ % 16 = 0 ∧ a₂ + 64 ≤ NA) (hb₂ : b₂ % 16 = 0 ∧ b₂ + 64 ≤ NA)
    (ho₁ : o₁ % 16 = 0 ∧ o₁ + 64 ≤ NA) (ho₂ : o₂ % 16 = 0 ∧ o₂ + 64 ≤ NA) (h12 : o₁ + 64 ≤ o₂ ∨ o₂ + 64 ≤ o₁)
    (la₁ : ∀ i < 8, limbs s.mem base a₁ i < Ib) (lb₁ : ∀ i < 8, limbs s.mem base b₁ i < Ib)
    (la₂ : ∀ i < 8, limbs s.mem base a₂ i < Ib) (lb₂ : ∀ i < 8, limbs s.mem base b₂ i < Ib) :
    WP isa (.block (mul2 o₁ a₁ b₁ o₂ a₂ b₂)) s fun t =>
      (∀ i < 8, limbs t.mem base o₁ i < Mb) ∧ (∀ i < 8, limbs t.mem base o₂ i < Mb) ∧
      toFe (valN (limbs t.mem base o₁) 8) =
        toFe (valN (limbs s.mem base a₁) 8) * toFe (valN (limbs s.mem base b₁) 8) ∧
      toFe (valN (limbs t.mem base o₂) 8) =
        toFe (valN (limbs s.mem base a₂) 8) * toFe (valN (limbs s.mem base b₂) 8) ∧
      (∀ x, (ofs base x < o₁ ∨ o₁ + 64 ≤ ofs base x) → (ofs base x < o₂ ∨ o₂ + 64 ≤ ofs base x) →
        (ofs base x < NA ∨ NA + 640 ≤ ofs base x) → t.mem x = s.mem x) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hNA : NA = 4096 := rfl
  rw [mul2_eq, WP.block_append_iff]
  refine WP.mono (prep_ok hs ha₁ hb₁ ha₂ hb₂ la₁ lb₁ la₂ lb₂) fun t1 ⟨hm, hM, h31, o1, g1, r1, w1⟩ => ?_
  obtain s1 : Scr t1 base := scr_of hs g1 w1
  rw [WP.block_append_iff]
  refine WP.mono (prods_ok s1 (X := fun e => L28 s.mem base a₁ a₂ e) (Y := fun e => L28 s.mem base b₁ b₂ e) hm h31)
    fun t2 ⟨l2, m2, g2, r2, w2, v2⟩ => ?_
  obtain kb : ∀ e < 2, ∀ k < 16, kara (L28 s.mem base a₁ a₂ e) (L28 s.mem base b₁ b₂ e) k < 2 ^ 64 - 2 ^ 40 :=
    fun e he k hk => kara_le (L28_le la₁ la₂ e he) (L28_le lb₁ lb₂ e he) hk
  obtain hb : ∀ e < 2, ∀ k < 16, (kara (L28 s.mem base a₁ a₂ e) (L28 s.mem base b₁ b₂ e) k).toNat < 2 ^ 64 - 2 ^ 40 :=
    fun e he k hk => toNat_lt (kb e he k hk)
  obtain hr : ∀ k < 16, LaneIs t2 k (fun e => (kara (L28 s.mem base a₁ a₂ e) (L28 s.mem base b₁ b₂ e) k).toNat) :=
    fun k hk e he => lane_exact (kara_nonneg _ _ _) (kb e he k hk) (l2 k hk e he)
  obtain hM2 : ∀ e < 2, (vdword (t2.v (V 30)) e).toNat = 2 ^ 28 - 1 := by
    rw [v2 _ (fun n hn => V_ne 30 (by decide) n (by omega_arith) (by omega_arith))]; exact hM
  rw [WP.block_append_iff]
  refine WP.mono (carries_ok _ hr hb hM2) fun t3 ⟨l3, m3, g3, r3, w3, v3⟩ => ?_
  obtain s3 : Scr t3 base := scr_of (scr_of s1 g2 w2) g3 w3
  refine WP.mono (finishN_ok s3 _ l3 (fun e he i hi => limbs28_even (hb e he) hi)
    (fun e he i hi => limbs28_odd (hb e he) hi) ho₁.1 (by omega_arith) ho₂.1 (by omega_arith) h12 (by
      rw [v3 _ (fun n _ => V_ne 30 (by decide) n (by omega_arith) (by omega_arith)) (by decide) (by decide)]; exact hM2))
    fun t4 ⟨f1, f2, o4, r4, w4, g4⟩ => ?_
  obtain val : ∀ e < 2, ∀ {fa fb : Nat → Nat}, L28 s.mem base a₁ a₂ e = l28 fa → L28 s.mem base b₁ b₂ e = l28 fb →
      toFe (valN (out56 (limbs28 fun k => (kara (L28 s.mem base a₁ a₂ e) (L28 s.mem base b₁ b₂ e) k).toNat)) 8) =
        toFe (valN fa 8) * toFe (valN fb 8) := fun e he fa fb ea eb =>
    mul2_val fa fb _ fun k _ => by rw [Int.toNat_of_nonneg (kara_nonneg _ _ _), ea, eb]
  refine ⟨fun i hi => (f1 i hi).symm ▸ out56_bound (hb 0 (by decide)) i hi,
    fun i hi => (f2 i hi).symm ▸ out56_bound (hb 1 (by decide)) i hi,
    (congrArg toFe (valN_congr f1)).trans (val 0 (by decide) rfl rfl),
    (congrArg toFe (valN_congr f2)).trans (val 1 (by decide) rfl rfl),
    fun x x1 x2 x3 => ?_, g4.trans (g3.trans (g2.trans g1)),
    r4.trans (r3.trans (r2.trans r1)), w4.trans (w3.trans (w2.trans w1))⟩
  rw [o4 x x1 x2, m3, m2]
  exact o1 x x3

end VG.Proof.Curve448.AArch64.Neon
