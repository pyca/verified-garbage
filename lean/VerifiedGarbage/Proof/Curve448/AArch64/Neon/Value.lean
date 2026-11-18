module

public import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Math
public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Bounds
public import VerifiedGarbage.Proof.X448.Field
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.TacticTemplate
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Convert
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Impl.Curve448.AArch64.Neon
public import VerifiedGarbage.Proof.Framework.Semantics
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Macs

/-! ### `Curve448.AArch64.Neon.Arith`, which this module and modules that import it used -/

section

/-!
# Lanes of the 64-bit lane arithmetic

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64

theorem lane_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat} (he : e < 2) :
    vdword (VArr.d2.map2 f x y) e = f 64 (vdword x e) (vdword y e) := by
  rcases (show e = 0 ∨ e = 1 by omega_using [he]) with rfl | rfl
  · exact map2_0 f x y
  · exact map2_1 f x y

theorem lane_add (x y : BitVec 128) {e : Nat} (he : e < 2) :
    lane (VArr.d2.map2 (fun _ a b => a + b) x y) e % M64 = (lane x e + lane y e) % M64 := by
  simp only [lane, lane_map2 _ _ _ he, BitVec.toNat_add]
  have h64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := rfl
  rw [Int.natCast_emod, Int.natCast_add, h64]
  exact Int.emod_emod_of_dvd _ (Int.dvd_refl _)

theorem lane_sub (x y : BitVec 128) {e : Nat} (he : e < 2) :
    lane (VArr.d2.map2 (fun _ a b => a - b) x y) e % M64 = (lane x e - lane y e) % M64 := by
  simp only [lane, lane_map2 _ _ _ he, BitVec.toNat_sub, M64]
  have := (vdword y e).isLt
  have h64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := rfl
  rw [Int.natCast_emod, Int.natCast_add, Int.ofNat_sub (Nat.le_of_lt this), h64,
    Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
  omega_using []

theorem lane_ushr (y x : BitVec 128) (sh : Nat) {e : Nat} (he : e < 2) :
    (vdword (VArr.d2.map2 (fun w a b => VShiftOp.eval .ushr sh w a b) y x) e).toNat = (vdword x e).toNat / 2 ^ sh := by
  rw [lane_map2 _ _ _ he]
  simp [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem lane_shl (y x : BitVec 128) (sh : Nat) {e : Nat} (he : e < 2) :
    (vdword (VArr.d2.map2 (fun w a b => VShiftOp.eval .shl sh w a b) y x) e).toNat =
      (vdword x e).toNat * 2 ^ sh % 2 ^ 64 := by
  rw [lane_map2 _ _ _ he]
  simp [VShiftOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem lane_and (x m : BitVec 128) {k : Nat} (hm : ∀ e < 2, (vdword m e).toNat = 2 ^ k - 1) {e : Nat} (he : e < 2) :
    (vdword (x &&& m) e).toNat = (vdword x e).toNat % 2 ^ k := by
  rw [vdword_and, BitVec.toNat_and, hm e he, Nat.and_two_pow_sub_one_eq_mod]

end VG.Proof.Curve448.AArch64.Neon

end

end

/-! ### `Curve448.AArch64.Neon.NFinish`, which only this module used -/

section

/-! ### `Curve448.AArch64.Neon.Carries`, which only this module used -/

section

/-!
# The coefficients' carries

Untrusted: everything here is checked by Lean. Two chains carry in radix
2²⁸, `0 → 7` and `8 → 15`; their last carries go to coefficients 8 and 0, by
`2⁴⁴⁸ = 2²²⁴ + 1`. With coefficients small enough, every lane holds its exact
value.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon

/-- The carry into coefficient `b + k` of the chain from `b`. -/
def cin (r : Nat → Nat) (b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (r (b + k) + cin r b k) / 2 ^ 28

/-- The value of coefficient `b + k` with its carry. -/
abbrev cval (r : Nat → Nat) (b k : Nat) : Nat := r (b + k) + cin r b k

abbrev C7 (r : Nat → Nat) : Nat := cval r 0 7 / 2 ^ 28
abbrev C15 (r : Nat → Nat) : Nat := cval r 8 7 / 2 ^ 28

/-- The limbs after the carries. -/
def limbs28 (r : Nat → Nat) (k : Nat) : Nat :=
  if k < 8 then cval r 0 k % 2 ^ 28 + (if k = 0 then C15 r else 0)
  else cval r 8 (k - 8) % 2 ^ 28 + (if k = 8 then C7 r + C15 r else 0)

/-- Lane `e` of vector register `r` is exactly `x e`. -/
abbrev LaneIs (t : State) (r : Nat) (x : Nat → Nat) : Prop := ∀ e < 2, (vdword (t.v (V r)) e).toNat = x e

theorem cin_le {r : Nat → Nat} {b : Nat} (hr : ∀ k < 8, r (b + k) < 2 ^ 64 - 2 ^ 40) : ∀ k ≤ 8, cin r b k < 2 ^ 36 := by
  intro k hk
  induction k with
  | zero => simp [cin]
  | succ k ih =>
    simp only [cin]
    have := ih (by omega_arith)
    have := hr k (by omega_arith)
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    omega_arith

/-- One step of a chain: carry out of `v_{b+k}` (through `v_t`) into `v_{b+k+1}`. -/
def chainStep (b k t : Nat) : List Instr :=
  [vo (.shift .ushr .d2 (V t) (V (b + k)) 28), vo (.logic .and (V (b + k)) (V (b + k)) (V 30)),
    vo (.add .d2 (V (b + k + 1)) (V (b + k + 1)) (V t))]

theorem chainStep_ok {s : State} {b k t : Nat} (hk : b + k + 1 < 16) (ht : 28 ≤ t ∧ t < 30)
    (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) {x y : Nat → Nat}
    (hx : LaneIs s (b + k) x) (hy : LaneIs s (b + k + 1) y) (hxy : ∀ e < 2, y e + x e / 2 ^ 28 < 2 ^ 64) :
    WP isa (.block (chainStep b k t)) s fun u =>
      LaneIs u (b + k) (fun e => x e % 2 ^ 28) ∧ LaneIs u (b + k + 1) (fun e => y e + x e / 2 ^ 28) ∧
      u.mem = s.mem ∧ u.gpr = s.gpr ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      (∀ r : VReg, r ≠ V t → r ≠ V (b + k) → r ≠ V (b + k + 1) → u.v r = s.v r) := by
  obtain n1 : V t ≠ V (b + k) := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  obtain n2 : V t ≠ V (b + k + 1) := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  obtain n3 : V (b + k) ≠ V (b + k + 1) := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  obtain n4 : V 30 ≠ V t := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  obtain n5 : V 30 ≠ V (b + k) := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  simp only [chainStep]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_nil_iff.mpr ⟨fun e he => ?_, fun e he => ?_, rfl, rfl, rfl, rfl, fun r h1 h2 h3 => ?_⟩
  · rw [RegUpd.v_setV_of_ne _ _ n3, RegUpd.v_setV_self, lane_and _ _ hM he, hx e he]
  · rw [RegUpd.v_setV_self, lane_map2 _ _ _ he, BitVec.toNat_add, lane_map2 _ _ _ he]
    simp only [VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx e he, hy e he]
    exact Nat.mod_eq_of_lt (hxy e he)
  · rw [RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ h2, RegUpd.v_setV_of_ne _ _ h1]

def wrap : List Instr :=
  [vo (.shift .ushr .d2 (V 28) (V 7) 28), vo (.logic .and (V 7) (V 7) (V 30)),
    vo (.shift .ushr .d2 (V 29) (V 15) 28), vo (.logic .and (V 15) (V 15) (V 30)),
    vo (.add .d2 (V 8) (V 8) (V 28)), vo (.add .d2 (V 8) (V 8) (V 29)), vo (.add .d2 (V 0) (V 0) (V 29))]

theorem carries_eq : carries = (List.range 7).flatMap (fun k => chainStep 0 k 28 ++ chainStep 8 k 29) ++ wrap := rfl

/-- Coefficient `b + k` of a chain after `n` steps. -/
def chainAt (r : Nat → Nat) (b n k : Nat) : Nat :=
  if k < n then cval r b k % 2 ^ 28 else if k = n then cval r b k else r (b + k)

theorem chainAt_zero (r : Nat → Nat) (b k : Nat) : chainAt r b 0 k = r (b + k) := by
  rcases k with _ | k <;> simp [chainAt, cval, cin]

/-- The chains, before the last carries. -/
theorem chainLoop_ok {s : State} (r : Nat → Nat → Nat) (hr : ∀ k < 16, LaneIs s k (fun e => r e k))
    (hb : ∀ e < 2, ∀ k < 16, r e k < 2 ^ 64 - 2 ^ 40) (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block ((List.range 7).flatMap (fun k => chainStep 0 k 28 ++ chainStep 8 k 29))) s fun t =>
      (∀ k < 8, LaneIs t k (fun e => chainAt (r e) 0 7 k)) ∧ (∀ k < 8, LaneIs t (8 + k) (fun e => chainAt (r e) 8 7 k)) ∧
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) ∧
      (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → t.v v = s.v v) := by
  obtain ci : ∀ e < 2, ∀ b ∈ [0, 8], ∀ k ≤ 8, cin (r e) b k < 2 ^ 36 := fun e he b hb' k hk =>
    cin_le (fun k hk => hb e he _ (by simp at hb'; omega_arith)) k hk
  let inv := fun n (t : State) =>
    (∀ k < 8, LaneIs t k (fun e => chainAt (r e) 0 n k)) ∧ (∀ k < 8, LaneIs t (8 + k) (fun e => chainAt (r e) 8 n k)) ∧
    t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) ∧
    (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → t.v v = s.v v)
  obtain i0 : inv 0 s := ⟨fun k hk e he => by dsimp only; rw [chainAt_zero, Nat.zero_add]; exact hr k (by omega_arith) e he,
    fun k hk e he => by dsimp only; rw [chainAt_zero]; exact hr (8 + k) (by omega_arith) e he,
    rfl, rfl, rfl, rfl, hM, fun _ _ _ _ => rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv (fun n t hn ⟨t0, t8, tm, tg, tr, tw, tM, tv⟩ => ?_) 7
    (by decide) s i0) fun t ht => ht
  · rw [WP.block_append_iff]
    obtain cn : ∀ e < 2, ∀ b ∈ [0, 8], chainAt (r e) b n n = cval (r e) b n := fun e _ b _ => by
      simp [chainAt]
    obtain cn1 : ∀ e < 2, ∀ b ∈ [0, 8], chainAt (r e) b n (n + 1) = r e (b + (n + 1)) := fun e _ b _ => by
      simp [chainAt, show ¬ (n + 1 < n) by omega_arith]
    obtain bnd : ∀ e < 2, ∀ b ∈ [0, 8], r e (b + (n + 1)) + cval (r e) b n / 2 ^ 28 < 2 ^ 64 := fun e he b hb' => by
      obtain h1 := ci e he b hb' (n + 1) (by omega_arith)
      obtain h2 := hb e he (b + (n + 1)) (by simp at hb'; omega_arith)
      simp only [cin] at h1
      simp only [cval]
      omega_arith
    refine WP.mono (chainStep_ok (b := 0) (k := n) (t := 28) (by omega_arith) (by omega_arith) tM
      (fun e he => by rw [Nat.zero_add, t0 n (by omega_arith) e he]; dsimp only; rw [cn e he 0 (by simp)])
      (fun e he => by rw [Nat.zero_add, t0 (n + 1) (by omega_arith) e he]; dsimp only; rw [cn1 e he 0 (by simp)])
      (fun e he => bnd e he 0 (by simp))) fun u ⟨ua, ub, um, ug, ur, uw, uv⟩ => ?_
    simp only [Nat.zero_add] at ua ub uv
    obtain u8 : ∀ k < 8, u.v (V (8 + k)) = t.v (V (8 + k)) := fun k hk =>
      uv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
        (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
    obtain uM : ∀ e < 2, (vdword (u.v (V 30)) e).toNat = 2 ^ 28 - 1 := fun e he => by
      rw [uv _ (by decide) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))]
      exact tM e he
    refine WP.mono (chainStep_ok (b := 8) (k := n) (t := 29) (by omega_arith) (by omega_arith) uM
      (fun e he => by rw [u8 n (by omega_arith), t8 n (by omega_arith) e he]; dsimp only; rw [cn e he 8 (by simp)])
      (fun e he => by
        rw [show 8 + n + 1 = 8 + (n + 1) by omega_arith, u8 (n + 1) (by omega_arith), t8 (n + 1) (by omega_arith) e he]
        dsimp only; rw [cn1 e he 8 (by simp)])
      (fun e he => bnd e he 8 (by simp))) fun w ⟨wa, wb, wm, wg, wr, ww, wv⟩ => ?_
    obtain w0 : ∀ k < 8, w.v (V k) = u.v (V k) := fun k hk =>
      wv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
        (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
    refine ⟨fun k hk e he => ?_, fun k hk e he => ?_, wm.trans (um.trans tm), wg.trans (ug.trans tg),
      wr.trans (ur.trans tr), ww.trans (uw.trans tw), fun e he => ?_, fun v h1 h2 h3 => ?_⟩
    · rw [w0 k hk]
      rcases (show k < n ∨ k = n ∨ k = n + 1 ∨ n + 1 < k by omega_arith) with h | rfl | rfl | h
      · rw [uv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
          (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), t0 k hk e he]
        simp [chainAt, h, show k < n + 1 by omega_arith]
      · rw [ua e he]; simp [chainAt]
      · rw [ub e he]; simp [chainAt, cval, cin]
      · rw [uv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
          (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), t0 k hk e he]
        simp [chainAt, show ¬ k < n by omega_arith, show k ≠ n by omega_arith, show ¬ k < n + 1 by omega_arith, show k ≠ n + 1 by omega_arith]
    · rcases (show k < n ∨ k = n ∨ k = n + 1 ∨ n + 1 < k by omega_arith) with h | rfl | rfl | h
      · rw [wv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
          (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), u8 k hk, t8 k hk e he]
        simp [chainAt, h, show k < n + 1 by omega_arith]
      · rw [wa e he]; simp [chainAt]
      · rw [show 8 + (n + 1) = 8 + n + 1 by omega_arith, wb e he]; simp [chainAt, cval, cin]
      · rw [wv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
          (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), u8 k hk, t8 k hk e he]
        simp [chainAt, show ¬ k < n by omega_arith, show k ≠ n by omega_arith, show ¬ k < n + 1 by omega_arith, show k ≠ n + 1 by omega_arith]
    · rw [wv _ (by decide) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))]
      exact uM e he
    · rw [wv _ h3 (h1 _ (by omega_arith)) (h1 _ (by omega_arith)), uv _ h2 (h1 _ (by omega_arith)) (h1 _ (by omega_arith)), tv v h1 h2 h3]

/-- The last carries: `C7` into coefficient 8, `C15` into 0 and 8. -/
theorem wrap_ok {t : State} (r : Nat → Nat → Nat) (hb : ∀ e < 2, ∀ k < 16, r e k < 2 ^ 64 - 2 ^ 40)
    (t0 : ∀ k < 8, LaneIs t k (fun e => chainAt (r e) 0 7 k)) (t8 : ∀ k < 8, LaneIs t (8 + k) (fun e => chainAt (r e) 8 7 k))
    (tM : ∀ e < 2, (vdword (t.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block wrap) t fun u =>
      (∀ k < 16, LaneIs u k (fun e => limbs28 (r e) k)) ∧ u.mem = t.mem ∧ u.gpr = t.gpr ∧ u.rd = t.rd ∧
      u.wr = t.wr ∧ (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → u.v v = t.v v) := by
  obtain ci : ∀ e < 2, ∀ b ∈ [0, 8], ∀ k ≤ 8, cin (r e) b k < 2 ^ 36 := fun e he b hb' k hk =>
    cin_le (fun k hk => hb e he _ (by simp at hb'; omega_arith)) k hk
  obtain c7 : ∀ e < 2, cval (r e) 0 7 / 2 ^ 28 < 2 ^ 36 := fun e he => by
    have := ci e he 0 (by simp) 8 (by omega_arith); simp only [cin] at this; exact this
  obtain c15 : ∀ e < 2, cval (r e) 8 7 / 2 ^ 28 < 2 ^ 36 := fun e he => by
    have := ci e he 8 (by simp) 8 (by omega_arith); simp only [cin] at this; exact this
  obtain n0_7 : V 0 ≠ V 7 := by decide
  obtain n0_8 : V 0 ≠ V 8 := by decide
  obtain n0_15 : V 0 ≠ V 15 := by decide
  obtain n0_28 : V 0 ≠ V 28 := by decide
  obtain n0_29 : V 0 ≠ V 29 := by decide
  obtain n0_30 : V 0 ≠ V 30 := by decide
  obtain n7_0 : V 7 ≠ V 0 := by decide
  obtain n7_8 : V 7 ≠ V 8 := by decide
  obtain n7_15 : V 7 ≠ V 15 := by decide
  obtain n7_28 : V 7 ≠ V 28 := by decide
  obtain n7_29 : V 7 ≠ V 29 := by decide
  obtain n7_30 : V 7 ≠ V 30 := by decide
  obtain n8_0 : V 8 ≠ V 0 := by decide
  obtain n8_7 : V 8 ≠ V 7 := by decide
  obtain n8_15 : V 8 ≠ V 15 := by decide
  obtain n8_28 : V 8 ≠ V 28 := by decide
  obtain n8_29 : V 8 ≠ V 29 := by decide
  obtain n8_30 : V 8 ≠ V 30 := by decide
  obtain n15_0 : V 15 ≠ V 0 := by decide
  obtain n15_7 : V 15 ≠ V 7 := by decide
  obtain n15_8 : V 15 ≠ V 8 := by decide
  obtain n15_28 : V 15 ≠ V 28 := by decide
  obtain n15_29 : V 15 ≠ V 29 := by decide
  obtain n15_30 : V 15 ≠ V 30 := by decide
  obtain n28_0 : V 28 ≠ V 0 := by decide
  obtain n28_7 : V 28 ≠ V 7 := by decide
  obtain n28_8 : V 28 ≠ V 8 := by decide
  obtain n28_15 : V 28 ≠ V 15 := by decide
  obtain n28_29 : V 28 ≠ V 29 := by decide
  obtain n28_30 : V 28 ≠ V 30 := by decide
  obtain n29_0 : V 29 ≠ V 0 := by decide
  obtain n29_7 : V 29 ≠ V 7 := by decide
  obtain n29_8 : V 29 ≠ V 8 := by decide
  obtain n29_15 : V 29 ≠ V 15 := by decide
  obtain n29_28 : V 29 ≠ V 28 := by decide
  obtain n29_30 : V 29 ≠ V 30 := by decide
  obtain n30_0 : V 30 ≠ V 0 := by decide
  obtain n30_7 : V 30 ≠ V 7 := by decide
  obtain n30_8 : V 30 ≠ V 8 := by decide
  obtain n30_15 : V 30 ≠ V 15 := by decide
  obtain n30_28 : V 30 ≠ V 28 := by decide
  obtain n30_29 : V 30 ≠ V 29 := by decide
  obtain l7 : ∀ e < 2, (vdword (t.v (V 7)) e).toNat = cval (r e) 0 7 := fun e he => by
    rw [t0 7 (by omega_arith) e he]; simp [chainAt]
  obtain l15 : ∀ e < 2, (vdword (t.v (V 15)) e).toNat = cval (r e) 8 7 := fun e he => by
    rw [t8 7 (by omega_arith) e he]; simp [chainAt]
  obtain l0 : ∀ e < 2, (vdword (t.v (V 0)) e).toNat = cval (r e) 0 0 % 2 ^ 28 := fun e he => by
    rw [t0 0 (by omega_arith) e he]; simp [chainAt]
  obtain l8 : ∀ e < 2, (vdword (t.v (V 8)) e).toNat = cval (r e) 8 0 % 2 ^ 28 := fun e he => by
    rw [t8 0 (by omega_arith) e he]; simp [chainAt]
  simp only [wrap]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr ?_⟩
  refine ⟨fun k hk e he => ?_, by simp only [RegUpd.mem_setV], by simp only [RegUpd.gpr_setV],
    by simp only [RegUpd.rd_setV], by simp only [RegUpd.wr_setV], fun v h1 h2 h3 => ?_⟩
  · rcases (show k = 0 ∨ k = 7 ∨ k = 8 ∨ k = 15 ∨ (0 < k ∧ k < 7) ∨ (8 < k ∧ k < 15) by omega_arith)
      with rfl | rfl | rfl | rfl | ⟨k1, k2⟩ | ⟨k1, k2⟩
    · vred
      rw [lane_map2 _ _ _ he, BitVec.toNat_add, l0 e he, ushr28 _ _ _ he, l15 e he]
      simp only [limbs28, show (0 : Nat) < 8 by decide, ite_true]
      have := c15 e he
      exact Nat.mod_eq_of_lt (by omega_arith)
    · vred
      rw [lane_and _ _ tM he, l7 e he]
      simp [limbs28]
    · vred
      rw [lane_map2 _ _ _ he, BitVec.toNat_add, lane_map2 _ _ _ he,
        BitVec.toNat_add, l8 e he, ushr28 _ _ _ he, l7 e he, ushr28 _ _ _ he, l15 e he]
      have := c7 e he; have := c15 e he
      rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
      simp only [limbs28, show ¬ (8 : Nat) < 8 by decide, ite_false, ite_true, Nat.sub_self, C7, C15]
      omega_arith
    · vred
      rw [lane_and _ _ tM he, l15 e he]
      simp [limbs28]
    · have hv : ∀ n ∈ [0, 7, 8, 15, 28, 29], V k ≠ V n := fun n hn =>
        V_ne _ (by omega_arith) _ (by simp at hn; omega_arith) (by simp at hn; omega_arith)
      rw [RegUpd.v_setV_of_ne _ _ (hv 0 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 15 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 29 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 7 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 28 (by simp)), t0 k (by omega_arith) e he]
      simp [chainAt, limbs28, show k < 7 by omega_arith, show k < 8 by omega_arith, show k ≠ 0 by omega_arith]
    · have hv : ∀ n ∈ [0, 7, 8, 15, 28, 29], V k ≠ V n := fun n hn =>
        V_ne _ (by omega_arith) _ (by simp at hn; omega_arith) (by simp at hn; omega_arith)
      rw [RegUpd.v_setV_of_ne _ _ (hv 0 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 8 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 15 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 29 (by simp)), RegUpd.v_setV_of_ne _ _ (hv 7 (by simp)),
        RegUpd.v_setV_of_ne _ _ (hv 28 (by simp)), show k = 8 + (k - 8) by omega_arith, t8 (k - 8) (by omega_arith) e he]
      simp [chainAt, limbs28, show k - 8 < 7 by omega_arith, show ¬ (8 + (k - 8) < 8) by omega_arith]
      intro h; omega_arith
  · rw [RegUpd.v_setV_of_ne _ _ (h1 0 (by decide)), RegUpd.v_setV_of_ne _ _ (h1 8 (by decide)),
      RegUpd.v_setV_of_ne _ _ (h1 8 (by decide)), RegUpd.v_setV_of_ne _ _ (h1 15 (by decide)),
      RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ (h1 7 (by decide)), RegUpd.v_setV_of_ne _ _ h2]

theorem carries_ok {s : State} (r : Nat → Nat → Nat) (hr : ∀ k < 16, LaneIs s k (fun e => r e k))
    (hb : ∀ e < 2, ∀ k < 16, r e k < 2 ^ 64 - 2 ^ 40) (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block carries) s fun t =>
      (∀ k < 16, LaneIs t k (fun e => limbs28 (r e) k)) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ v : VReg, (∀ n < 16, v ≠ V n) → v ≠ V 28 → v ≠ V 29 → t.v v = s.v v) := by
  rw [carries_eq, WP.block_append_iff]
  exact WP.mono (chainLoop_ok r hr hb hM) fun t ⟨t0, t8, tm, tg, tr, tw, tM, tv⟩ =>
    WP.mono (wrap_ok r hb t0 t8 tM) fun u ⟨ul, um, ug, ur, uw, uv⟩ =>
      ⟨ul, um.trans tm, ug.trans tg, ur.trans tr, uw.trans tw, fun v h1 h2 h3 => (uv v h1 h2 h3).trans (tv v h1 h2 h3)⟩

/-! ## The value -/

/-- `Σ_{k<n} f k xᵏ`. -/
def psum (f : Nat → Nat) (x : Int) : Nat → Int
  | 0 => 0
  | n + 1 => psum f x n + f n * x ^ n

/-- A chain keeps the value: its limbs and its last carry are its coefficients. -/
theorem chain_val (r : Nat → Nat) (b : Nat) (n : Nat) :
    psum (fun k => cval r b k % 2 ^ 28) (2 ^ 28) n + cin r b n * (2 ^ 28 : Int) ^ n =
      psum (fun k => r (b + k)) (2 ^ 28) n := by
  induction n with
  | zero => simp [psum, cin]
  | succ n ih =>
    simp only [psum, cin]
    obtain e' : cval r b n % 2 ^ 28 + (cval r b n / 2 ^ 28) * 2 ^ 28 = r (b + n) + cin r b n := by
      simp only [cval]; omega_arith
    obtain e : ((cval r b n % 2 ^ 28 : Nat) : Int) + ((cval r b n / 2 ^ 28 : Nat) : Int) * 2 ^ 28 =
        (r (b + n) : Int) + cin r b n := by exact_mod_cast e'
    rw [← ih]
    have : ((cval r b n % 2 ^ 28 : Nat) : Int) * (2 ^ 28) ^ n + ((cval r b n / 2 ^ 28 : Nat) : Int) * (2 ^ 28) ^ (n + 1) =
        ((r (b + n) : Int) + cin r b n) * (2 ^ 28) ^ n := by rw [← e]; ring
    linarith

theorem limbs28_val (r : Nat → Nat) :
    psum (limbs28 r) (2 ^ 28) 16 = psum r (2 ^ 28) 16 - (C15 r : Int) * ((2 ^ 28) ^ 16 - (2 ^ 28) ^ 8 - 1) := by
  obtain h0 := chain_val r 0 8
  obtain h8 := chain_val r 8 8
  have c7 : cin r 0 8 = C7 r := rfl
  have c15 : cin r 8 8 = C15 r := rfl
  rw [c7] at h0
  rw [c15] at h8
  simp only [psum, limbs28, Nat.zero_add] at h0 h8 ⊢
  simp only [show (0 : Nat) < 8 by decide, show (1 : Nat) < 8 by decide, show (2 : Nat) < 8 by decide,
    show (3 : Nat) < 8 by decide, show (4 : Nat) < 8 by decide, show (5 : Nat) < 8 by decide,
    show (6 : Nat) < 8 by decide, show (7 : Nat) < 8 by decide, show ¬ (8 : Nat) < 8 by decide,
    show ¬ (9 : Nat) < 8 by decide, show ¬ (10 : Nat) < 8 by decide, show ¬ (11 : Nat) < 8 by decide,
    show ¬ (12 : Nat) < 8 by decide, show ¬ (13 : Nat) < 8 by decide, show ¬ (14 : Nat) < 8 by decide,
    show ¬ (15 : Nat) < 8 by decide, ite_true, ite_false, Nat.reduceSub, Nat.cast_add,
    ] at ⊢
  simp only [show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide,
    show (4 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 0 by decide,
    show (7 : Nat) ≠ 0 by decide, show (9 : Nat) ≠ 8 by decide, show (10 : Nat) ≠ 8 by decide,
    show (11 : Nat) ≠ 8 by decide, show (12 : Nat) ≠ 8 by decide, show (13 : Nat) ≠ 8 by decide,
    show (14 : Nat) ≠ 8 by decide, show (15 : Nat) ≠ 8 by decide, ite_false, 
    Nat.cast_zero, Int.add_zero] at ⊢
  linear_combination h0 + (2 ^ 28) ^ 8 * h8

end VG.Proof.Curve448.AArch64.Neon

end

end

/-!
# The radix-2⁵⁶ results

Untrusted: everything here is checked by Lean. The sixteen radix-2²⁸ limbs
become eight radix-2⁵⁶ limbs, limbs 0 and 4 carry into 1 and 5, and the
two elements' limbs are stored.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside word limbs)

theorem word_st (m : Mem) (base : Addr) (d : Nat) (v : BitVec 128) {e : Nat} (he : e < 2) :
    word (m.write (off base d) 16 v) base (d + 8 * e) = vdword v e := by
  simp only [word]
  rw [← off_add, ← vdword_read16 _ _ he, read16_write]

def combineChunk (i : Nat) : List Instr :=
  [vo (.shift .shl .d2 (V (16 + i)) (V (2 * i + 1)) 28), vo (.add .d2 (V (16 + i)) (V (16 + i)) (V (2 * i)))]

def m56 : List Instr :=
  [vo (.shift .shl .d2 (V 31) (V 30) 28), vo (.add .d2 (V 31) (V 31) (V 30))]

def carry56 (i : Nat) : List Instr :=
  [vo (.shift .ushr .d2 (V 28) (V i) 56), vo (.logic .and (V i) (V i) (V 31)),
    vo (.add .d2 (V (i + 1)) (V (i + 1)) (V 28))]

def outChunk (o₁ o₂ k : Nat) : List Instr :=
  [vo (.perm .trn1 .d2 (V 8) (V (16 + 2 * k)) (V (17 + 2 * k))),
    vo (.perm .trn2 .d2 (V 9) (V (16 + 2 * k)) (V (17 + 2 * k))), stq 8 (o₁ + 16 * k), stq 9 (o₂ + 16 * k)]

theorem finish_eq (o₁ o₂ : Nat) :
    finish o₁ o₂ = (List.range 8).flatMap combineChunk ++ m56 ++ ([16, 20].flatMap carry56) ++
      (List.range 4).flatMap (outChunk o₁ o₂) := rfl

theorem combineChunk_ok {s : State} {i : Nat} (hi : i < 8) {lo hi' : Nat → Nat}
    (hl : LaneIs s (2 * i) lo) (hh : LaneIs s (2 * i + 1) hi') (hlo : ∀ e < 2, lo e < 2 ^ 63)
    (hhi : ∀ e < 2, hi' e < 2 ^ 28) :
    WP isa (.block (combineChunk i)) s fun t =>
      LaneIs t (16 + i) (fun e => lo e + 2 ^ 28 * hi' e) ∧ t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ r : VReg, r ≠ V (16 + i) → t.v r = s.v r) := by
  obtain n1 : V (2 * i + 1) ≠ V (16 + i) := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  obtain n2 : V (2 * i) ≠ V (16 + i) := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  simp only [combineChunk]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr ⟨fun e he => ?_,
    by simp only [RegUpd.mem_setV], by simp only [RegUpd.gpr_setV], by simp only [RegUpd.rd_setV],
    by simp only [RegUpd.wr_setV], fun r hr => ?_⟩⟩
  · rw [RegUpd.v_setV_self, lane_map2 _ _ _ he, BitVec.toNat_add, RegUpd.v_setV_self, lane_shl _ _ _ he,
      RegUpd.v_setV_of_ne _ _ n2, hl e he, hh e he]
    have := hlo e he; have := hhi e he
    rw [Nat.mod_eq_of_lt (by omega_arith : hi' e * 2 ^ 28 < 2 ^ 64), Nat.mod_eq_of_lt (by omega_arith)]
    dsimp only
    omega_arith
  · rw [RegUpd.v_setV_of_ne _ _ hr, RegUpd.v_setV_of_ne _ _ hr]

theorem combine_ok {s : State} (L : Nat → Nat → Nat) (hL : ∀ k < 16, LaneIs s k (L k))
    (he : ∀ i < 8, ∀ e < 2, L (2 * i) e < 2 ^ 63) (ho : ∀ i < 8, ∀ e < 2, L (2 * i + 1) e < 2 ^ 28) :
    WP isa (.block ((List.range 8).flatMap combineChunk)) s fun t =>
      (∀ i < 8, LaneIs t (16 + i) (fun e => L (2 * i) e + 2 ^ 28 * L (2 * i + 1) e)) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, (∀ i < 8, r ≠ V (16 + i)) → t.v r = s.v r) := by
  let inv := fun n (t : State) =>
    (∀ i < n, LaneIs t (16 + i) (fun e => L (2 * i) e + 2 ^ 28 * L (2 * i + 1) e)) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, (∀ i < n, r ≠ V (16 + i)) → t.v r = s.v r)
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨ti, tm, tg, tr, tw, tv⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (by omega_arith), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  obtain keep : ∀ k < 16, t.v (V k) = s.v (V k) := fun k hk =>
    tv _ fun i hi => V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  refine WP.mono (combineChunk_ok hn (fun e he' => by rw [keep _ (by omega_arith)]; exact hL _ (by omega_arith) e he')
    (fun e he' => by rw [keep _ (by omega_arith)]; exact hL _ (by omega_arith) e he') (he n hn) (ho n hn))
    fun u ⟨ua, um, ug, ur, uw, uv⟩ => ⟨fun i hi => ?_, um.trans tm, ug.trans tg, ur.trans tr, uw.trans tw,
      fun r hr => (uv r (hr n (by omega_arith))).trans (tv r fun i hi => hr i (by omega_arith))⟩
  rcases (show i < n ∨ i = n by omega_arith) with h | rfl
  · intro e he'
    rw [uv _ (V_ne (16 + i) (by omega_arith) (16 + n) (by omega_arith) (by omega_arith))]
    exact ti i h e he'
  · exact ua

theorem m56_ok {s : State} (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block m56) s fun t =>
      (∀ e < 2, (vdword (t.v (V 31)) e).toNat = 2 ^ 56 - 1) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr = s.gpr ∧ (∀ r : VReg, r ≠ V 31 → t.v r = s.v r) := by
  obtain n : V 30 ≠ V 31 := by decide
  simp only [m56]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr ⟨fun e he => ?_,
    by simp only [RegUpd.mem_setV], by simp only [RegUpd.rd_setV], by simp only [RegUpd.wr_setV],
    by simp only [RegUpd.gpr_setV], fun r hr => ?_⟩⟩
  · rw [RegUpd.v_setV_self, lane_map2 _ _ _ he, BitVec.toNat_add, RegUpd.v_setV_of_ne _ _ n, RegUpd.v_setV_self,
      lane_shl _ _ _ he, hM e he]
    decide
  · rw [RegUpd.v_setV_of_ne _ _ hr, RegUpd.v_setV_of_ne _ _ hr]

theorem carry56_ok {s : State} {i : Nat} (hi : i = 16 ∨ i = 20)
    (hM : ∀ e < 2, (vdword (s.v (V 31)) e).toNat = 2 ^ 56 - 1) {x y : Nat → Nat}
    (hx : LaneIs s i x) (hy : LaneIs s (i + 1) y) (hxy : ∀ e < 2, y e + x e / 2 ^ 56 < 2 ^ 64) :
    WP isa (.block (carry56 i)) s fun t =>
      LaneIs t i (fun e => x e % 2 ^ 56) ∧ LaneIs t (i + 1) (fun e => y e + x e / 2 ^ 56) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r : VReg, r ≠ V 28 → r ≠ V i → r ≠ V (i + 1) → t.v r = s.v r) := by
  obtain n1 : V 28 ≠ V i := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  obtain n2 : V 28 ≠ V (i + 1) := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  obtain n3 : V i ≠ V (i + 1) := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  obtain n4 : V 31 ≠ V 28 := by decide
  obtain n5 : V 31 ≠ V i := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  simp only [carry56]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, WP.block_nil_iff.mpr ⟨fun e he => ?_, fun e he => ?_,
    by simp only [RegUpd.mem_setV], by simp only [RegUpd.gpr_setV], by simp only [RegUpd.rd_setV],
    by simp only [RegUpd.wr_setV], fun r h1 h2 h3 => ?_⟩⟩
  · rw [RegUpd.v_setV_of_ne _ _ n3, RegUpd.v_setV_self, lane_and _ _ hM he, hx e he]
  · rw [RegUpd.v_setV_self, lane_map2 _ _ _ he, BitVec.toNat_add, RegUpd.v_setV_of_ne _ _ n3',
      RegUpd.v_setV_of_ne _ _ n2', RegUpd.v_setV_of_ne _ _ n1, RegUpd.v_setV_self, lane_ushr _ _ _ he, hx e he,
      hy e he]
    exact Nat.mod_eq_of_lt (hxy e he)
  · rw [RegUpd.v_setV_of_ne _ _ h3, RegUpd.v_setV_of_ne _ _ h2, RegUpd.v_setV_of_ne _ _ h1]

theorem outChunk_ok {s : State} {base : Addr} (hs : Scr s base) {o₁ o₂ k : Nat} (hk : k < 4)
    (h₁ : o₁ % 16 = 0) (h₁' : o₁ + 64 ≤ 8192) (h₂ : o₂ % 16 = 0) (h₂' : o₂ + 64 ≤ 8192)
    (h12 : o₁ + 64 ≤ o₂ ∨ o₂ + 64 ≤ o₁) :
    WP isa (.block (outChunk o₁ o₂ k)) s fun t =>
      (∀ j < 2, word t.mem base (o₁ + 8 * (2 * k + j)) = vdword (s.v (V (16 + (2 * k + j)))) 0) ∧
      (∀ j < 2, word t.mem base (o₂ + 8 * (2 * k + j)) = vdword (s.v (V (16 + (2 * k + j)))) 1) ∧
      VG.Proof.X448.AArch64.Outside2 base (o₁ + 16 * k) 16 (o₂ + 16 * k) 16 s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r : VReg, r ≠ V 8 → r ≠ V 9 → t.v r = s.v r) := by
  obtain n89 : V 8 ≠ V 9 := by decide
  have n98 := n89.symm
  obtain a8 : V (16 + 2 * k) ≠ V 8 := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  obtain b8 : V (17 + 2 * k) ≠ V 8 := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  obtain a9 : V (16 + 2 * k) ≠ V 9 := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  obtain b9 : V (17 + 2 * k) ≠ V 9 := V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)
  simp only [outChunk]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo_of rfl, ?_⟩
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?g1 8 (by omega_arith) (by omega_arith), ?_⟩
  case g1 => scr
  vred
  refine WP.block_cons_iff.mpr ⟨_, exec_stq (base := base) ?g2 9 (by omega_arith) (by omega_arith), ?_⟩
  case g2 => scr
  refine WP.block_nil_iff.mpr ⟨fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, fun r h8 h9 => ?_⟩
  · simp only [setMem_mem]
    rw [VG.Proof.X448.AArch64.Outside.word (st_outside _ base _ (by omega_arith)) (by omega_arith) (by omega_arith),
      show o₁ + 8 * (2 * k + j) = o₁ + 16 * k + 8 * j by omega_arith, word_st _ _ _ _ hj]
    rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl
    · rw [trn1_0]; rfl
    · rw [trn1_1, show 17 + 2 * k = 16 + (2 * k + 1) by omega_arith]
  · simp only [setMem_mem, setMem_v]
    rw [show o₂ + 8 * (2 * k + j) = o₂ + 16 * k + 8 * j by omega_arith, word_st _ _ _ _ hj, RegUpd.v_setV_self]
    rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl
    · rw [trn2_0]; rfl
    · rw [trn2_1, show 17 + 2 * k = 16 + (2 * k + 1) by omega_arith]
  · simp only [setMem_mem]
    intro p hp hq
    rw [st_outside _ base _ (by omega_arith) p hq, st_outside _ base _ (by omega_arith) p hp]
  · simp only [setMem_gpr, RegUpd.gpr_setV]
  · simp only [setMem_rd, RegUpd.rd_setV]
  · simp only [setMem_wr, RegUpd.wr_setV]
  · simp only [setMem_v, RegUpd.v_setV_of_ne _ _ h9, RegUpd.v_setV_of_ne _ _ h8]

/-- The radix-2⁵⁶ limbs of the sixteen limbs `L`, before the last carries. -/
abbrev w56 (L : Nat → Nat) (i : Nat) : Nat := L (2 * i) + 2 ^ 28 * L (2 * i + 1)

/-- The results: limbs 0 and 4 carried into 1 and 5. -/
def out56 (L : Nat → Nat) (i : Nat) : Nat :=
  if i = 0 then w56 L 0 % 2 ^ 56 else if i = 1 then w56 L 1 + w56 L 0 / 2 ^ 56
  else if i = 4 then w56 L 4 % 2 ^ 56 else if i = 5 then w56 L 5 + w56 L 4 / 2 ^ 56 else w56 L i

theorem finishN_ok {s : State} {base : Addr} (hs : Scr s base) {o₁ o₂ : Nat} (L : Nat → Nat → Nat)
    (hL : ∀ k < 16, LaneIs s k (fun e => L e k))
    (he : ∀ e < 2, ∀ i < 8, L e (2 * i) < 2 ^ 40) (ho : ∀ e < 2, ∀ i < 8, L e (2 * i + 1) < 2 ^ 28)
    (h₁ : o₁ % 16 = 0) (h₁' : o₁ + 64 ≤ 8192) (h₂ : o₂ % 16 = 0) (h₂' : o₂ + 64 ≤ 8192)
    (h12 : o₁ + 64 ≤ o₂ ∨ o₂ + 64 ≤ o₁) (hM : ∀ e < 2, (vdword (s.v (V 30)) e).toNat = 2 ^ 28 - 1) :
    WP isa (.block (finish o₁ o₂)) s fun t =>
      (∀ i < 8, limbs t.mem base o₁ i = out56 (L 0) i) ∧ (∀ i < 8, limbs t.mem base o₂ i = out56 (L 1) i) ∧
      VG.Proof.X448.AArch64.Outside2 base o₁ 64 o₂ 64 s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr = s.gpr := by
  rw [finish_eq, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (combine_ok (fun k e => L e k) hL (fun i hi e he' => by have := he e he' i hi; omega_arith)
    (fun i hi e he' => ho e he' i hi)) fun t ⟨tw, tm, tg, tr, twr, tv⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (m56_ok (fun e he' => by
    rw [tv _ (fun i _ => V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))]; exact hM e he')) fun u ⟨uM, um, ur, uw, ug, uv⟩ => ?_
  obtain hu : ∀ i < 8, LaneIs u (16 + i) (fun e => w56 (L e) i) := fun i hi e he' => by
    rw [uv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))]; exact tw i hi e he'
  rw [WP.block_append_iff]
  -- the last carries
  obtain b0 : ∀ e < 2, ∀ i < 8, w56 (L e) i < 2 ^ 57 := fun e he' i hi => by
    have := he e he' i hi; have := ho e he' i hi; simp only [w56]; omega_arith
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [WP.block_append_iff]
  refine WP.mono (carry56_ok (i := 16) (Or.inl rfl) uM (hu 0 (by decide)) (hu 1 (by decide))
    (fun e he' => by have := b0 e he' 1 (by decide); have := b0 e he' 0 (by decide); omega_arith))
    fun v ⟨va, vb, vm, vg, vr, vw, vv⟩ => ?_
  obtain vM : ∀ e < 2, (vdword (v.v (V 31)) e).toNat = 2 ^ 56 - 1 := fun e he' => by
    rw [vv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
      (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))]; exact uM e he'
  obtain v4 : LaneIs v 20 (fun e => w56 (L e) 4) := fun e he' => by
    rw [vv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
      (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))]; exact hu 4 (by decide) e he'
  obtain v5 : LaneIs v 21 (fun e => w56 (L e) 5) := fun e he' => by
    rw [vv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
      (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))]; exact hu 5 (by decide) e he'
  refine WP.mono (carry56_ok (i := 20) (Or.inr rfl) vM v4 v5
    (fun e he' => by have := b0 e he' 5 (by decide); have := b0 e he' 4 (by decide); omega_arith))
    fun w ⟨wa, wb, wm, wg, wr, ww, wv⟩ => ?_
  -- the results
  obtain wl : ∀ i < 8, LaneIs w (16 + i) (fun e => out56 (L e) i) := by
    intro i hi e he'
    rcases (show i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5 ∨ (i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 4 ∧ i ≠ 5) by omega_arith)
      with rfl | rfl | rfl | rfl | ⟨i0, i1, i4, i5⟩
    · rw [wv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
        (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), va e he']; simp [out56]
    · rw [wv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
        (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), vb e he']; simp [out56]
    · rw [wa e he']; simp [out56]
    · rw [wb e he']; simp [out56]
    · rw [wv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
        (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)),
        vv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
        (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)), hu i hi e he']
      simp [out56, i0, i1, i4, i5]
  obtain gw : w.gpr = s.gpr := by rw [wg, vg, ug, tg]
  obtain hw : Scr w base := scr_of hs gw (by rw [ww, vw, uw, twr])
  let inv := fun n (x : State) =>
    (∀ i < 2 * n, (word x.mem base (o₁ + 8 * i)).toNat = out56 (L 0) i) ∧
    (∀ i < 2 * n, (word x.mem base (o₂ + 8 * i)).toNat = out56 (L 1) i) ∧
    VG.Proof.X448.AArch64.Outside2 base o₁ 64 o₂ 64 w.mem x.mem ∧ x.gpr = w.gpr ∧ x.rd = w.rd ∧ x.wr = w.wr ∧
    (∀ i < 8, x.v (V (16 + i)) = w.v (V (16 + i)))
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) inv (fun n x hn ⟨x1, x2, xo, xg, xr, xw, xv⟩ => ?_) 4
    (by decide) w ⟨fun _ h => absurd h (by omega_arith), fun _ h => absurd h (by omega_arith),
      VG.Proof.X448.AArch64.Outside2.refl _ _ _ _ _ _, rfl, rfl, rfl, fun _ _ => rfl⟩)
    fun x ⟨x1, x2, xo, xg, xr, xw, _⟩ => ⟨fun i hi => x1 i (by omega_arith), fun i hi => x2 i (by omega_arith), ?_,
      by rw [xr, wr, vr, ur, tr], by rw [xw, ww, vw, uw, twr], by rw [xg, gw]⟩
  · have hx : Scr x base := ⟨by rw [xg]; exact hw.x3, by rw [xg]; exact hw.mask, xw ▸ hw.wr, hw.nowrap⟩
    refine WP.mono (outChunk_ok hx hn h₁ h₁' h₂ h₂' h12) fun y ⟨y1, y2, yo, yg, yr, yw, yv⟩ =>
      ⟨fun i hi => ?_, fun i hi => ?_, xo.trans fun p hp hq => yo p (by omega_arith) (by omega_arith), yg.trans xg,
        yr.trans xr, yw.trans xw, fun i hi => (yv _ (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))
          (V_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith))).trans (xv i hi)⟩
    · rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega_arith) with h | rfl | rfl
      · rw [VG.Proof.X448.AArch64.Outside2.word (fun p hp hq => yo p hp hq) (by omega_arith) (by omega_arith) (by omega_arith)]
        exact x1 i h
      · rw [show o₁ + 8 * (2 * n) = o₁ + 8 * (2 * n + 0) by omega_arith, y1 0 (by decide), xv _ (by omega_arith)]
        exact wl _ (by omega_arith) 0 (by decide)
      · rw [y1 1 (by decide), xv _ (by omega_arith)]
        exact wl _ (by omega_arith) 0 (by decide)
    · rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega_arith) with h | rfl | rfl
      · rw [VG.Proof.X448.AArch64.Outside2.word (fun p hp hq => yo p hp hq) (by omega_arith) (by omega_arith) (by omega_arith)]
        exact x2 i h
      · rw [show o₂ + 8 * (2 * n) = o₂ + 8 * (2 * n + 0) by omega_arith, y2 0 (by decide), xv _ (by omega_arith)]
        exact wl _ (by omega_arith) 1 (by decide)
      · rw [y2 1 (by decide), xv _ (by omega_arith)]
        exact wl _ (by omega_arith) 1 (by decide)
  · intro p hp hq
    rw [xo p hp hq, wm, vm, um, tm]

end VG.Proof.Curve448.AArch64.Neon

end

end

/-!
# The value and bounds of `mul2`'s results

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Neon

open VG.Proof.X448.Wide (valN)
open VG.Proof.X448 (toFe toFe_mul)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

/-- The radix-2²⁸ limbs of radix-2⁵⁶ limbs `f`. -/
def l28 (f : Nat → Nat) (k : Nat) : Nat := if k % 2 = 0 then f (k / 2) % 2 ^ 28 else f (k / 2) / 2 ^ 28

theorem psum_l28 (f : Nat → Nat) : psum (l28 f) (2 ^ 28) 16 = (valN f 8 : Int) := by
  have h : ∀ i, (f i : Int) % 268435456 + (f i : Int) / 268435456 * 268435456 = f i := fun i =>
    Int.emod_add_ediv_mul _ _
  simp only [psum, l28, valN, VG.Proof.X448.Wide.radix, Nat.reduceMod, Nat.reduceDiv, ite_true, ite_false,
    one_ne_zero]
  push_cast
  linear_combination h 0 + (72057594037927936 : Int) ^ 1 * h 1 + (72057594037927936 : Int) ^ 2 * h 2 + (72057594037927936 : Int) ^ 3 * h 3 + (72057594037927936 : Int) ^ 4 * h 4 + (72057594037927936 : Int) ^ 5 * h 5 + (72057594037927936 : Int) ^ 6 * h 6 + (72057594037927936 : Int) ^ 7 * h 7

theorem val_out56 (L : Nat → Nat) : (valN (out56 L) 8 : Int) = psum L (2 ^ 28) 16 := by
  simp only [valN, out56, psum, VG.Proof.X448.Wide.radix, w56]
  simp only [show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide, show (4 : Nat) ≠ 0 by decide,
    show (4 : Nat) ≠ 1 by decide, show (5 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 1 by decide,
    show (5 : Nat) ≠ 4 by decide, show (6 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 1 by decide,
    show (6 : Nat) ≠ 4 by decide, show (6 : Nat) ≠ 5 by decide, show (7 : Nat) ≠ 0 by decide,
    show (7 : Nat) ≠ 1 by decide, show (7 : Nat) ≠ 4 by decide, show (7 : Nat) ≠ 5 by decide, ite_true, ite_false]
  push_cast
  have h0 := Int.emod_add_ediv_mul ((L 0 : Int) + 268435456 * L 1) 72057594037927936
  have h4 := Int.emod_add_ediv_mul ((L 8 : Int) + 268435456 * L 9) 72057594037927936
  linear_combination h0 + (72057594037927936 : Int) ^ 4 * h4

theorem sum_l28 (f : Nat → Nat) : (l28 f 0 : Int) * (2 ^ 28 : Int) ^ 0 + (l28 f 1 : Int) * (2 ^ 28 : Int) ^ 1 + (l28 f 2 : Int) * (2 ^ 28 : Int) ^ 2 + (l28 f 3 : Int) * (2 ^ 28 : Int) ^ 3 + (l28 f 4 : Int) * (2 ^ 28 : Int) ^ 4 + (l28 f 5 : Int) * (2 ^ 28 : Int) ^ 5 + (l28 f 6 : Int) * (2 ^ 28 : Int) ^ 6 + (l28 f 7 : Int) * (2 ^ 28 : Int) ^ 7 + (l28 f 8 : Int) * (2 ^ 28 : Int) ^ 8 + (l28 f 9 : Int) * (2 ^ 28 : Int) ^ 9 + (l28 f 10 : Int) * (2 ^ 28 : Int) ^ 10 + (l28 f 11 : Int) * (2 ^ 28 : Int) ^ 11 + (l28 f 12 : Int) * (2 ^ 28 : Int) ^ 12 + (l28 f 13 : Int) * (2 ^ 28 : Int) ^ 13 + (l28 f 14 : Int) * (2 ^ 28 : Int) ^ 14 + (l28 f 15 : Int) * (2 ^ 28 : Int) ^ 15 = (valN f 8 : Int) := by
  have := psum_l28 f
  simp only [psum, Int.zero_add] at this
  exact this

theorem kara_ex (X : Int) (a b : Nat → Nat) :
    ∃ W : Int, ((a 0 : Int) * X ^ 0 + (a 1 : Int) * X ^ 1 + (a 2 : Int) * X ^ 2 + (a 3 : Int) * X ^ 3 + (a 4 : Int) * X ^ 4 + (a 5 : Int) * X ^ 5 + (a 6 : Int) * X ^ 6 + (a 7 : Int) * X ^ 7 + (a 8 : Int) * X ^ 8 + (a 9 : Int) * X ^ 9 + (a 10 : Int) * X ^ 10 + (a 11 : Int) * X ^ 11 + (a 12 : Int) * X ^ 12 + (a 13 : Int) * X ^ 13 + (a 14 : Int) * X ^ 14 + (a 15 : Int) * X ^ 15) * ((b 0 : Int) * X ^ 0 + (b 1 : Int) * X ^ 1 + (b 2 : Int) * X ^ 2 + (b 3 : Int) * X ^ 3 + (b 4 : Int) * X ^ 4 + (b 5 : Int) * X ^ 5 + (b 6 : Int) * X ^ 6 + (b 7 : Int) * X ^ 7 + (b 8 : Int) * X ^ 8 + (b 9 : Int) * X ^ 9 + (b 10 : Int) * X ^ 10 + (b 11 : Int) * X ^ 11 + (b 12 : Int) * X ^ 12 + (b 13 : Int) * X ^ 13 + (b 14 : Int) * X ^ 14 + (b 15 : Int) * X ^ 15) - (kara a b 0 * X ^ 0 + kara a b 1 * X ^ 1 + kara a b 2 * X ^ 2 + kara a b 3 * X ^ 3 + kara a b 4 * X ^ 4 + kara a b 5 * X ^ 5 + kara a b 6 * X ^ 6 + kara a b 7 * X ^ 7 + kara a b 8 * X ^ 8 + kara a b 9 * X ^ 9 + kara a b 10 * X ^ 10 + kara a b 11 * X ^ 11 + kara a b 12 * X ^ 12 + kara a b 13 * X ^ 13 + kara a b 14 * X ^ 14 + kara a b 15 * X ^ 15) = (X ^ 16 - X ^ 8 - 1) * W := ⟨_, kara_sum X a b⟩

/-- The value of a result of `mul2`: the product of the operands, modulo `p`. -/
theorem mul2_val (fa fb r : Nat → Nat) (hr : ∀ k < 16, (r k : Int) = kara (l28 fa) (l28 fb) k) :
    toFe (valN (out56 (limbs28 r)) 8) = toFe (valN fa 8) * toFe (valN fb 8) := by
  apply toFe_mul
  have hP : ((VG.Spec.X448.P : Nat) : Int) = (2 ^ 28) ^ 16 - (2 ^ 28) ^ 8 - 1 := by
    have h := VG.Proof.X448.full_eq
    simp only [VG.Proof.X448.full, VG.Proof.X448.half, VG.Proof.X448.radix] at h
    have h' : (((2 ^ 28) ^ 16 : Nat) : Int) = (VG.Spec.X448.P : Nat) + (((2 ^ 28) ^ 8 : Nat) : Int) + 1 := by
      rw [h]; push_cast; ring
    push_cast at h'
    linarith
  obtain ⟨W, hW⟩ := kara_ex (2 ^ 28) (l28 fa) (l28 fb)
  rw [sum_l28 fa, sum_l28 fb] at hW
  have e1 := val_out56 (limbs28 r)
  have e2 := limbs28_val r
  simp only [psum] at e1 e2
  rw [hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide), hr 4 (by decide), hr 5 (by decide), hr 6 (by decide), hr 7 (by decide), hr 8 (by decide), hr 9 (by decide), hr 10 (by decide), hr 11 (by decide), hr 12 (by decide), hr 13 (by decide), hr 14 (by decide), hr 15 (by decide)] at e2
  generalize (2 ^ 28 : Int) = X at *
  have key : (valN (out56 (limbs28 r)) 8 : Int) =
      (valN fa 8 : Int) * (valN fb 8 : Int) + (X ^ 16 - X ^ 8 - 1) * (-W - C15 r) := by
    linear_combination e1 + e2 - hW
  have : ((valN (out56 (limbs28 r)) 8 : Nat) : Int) % (VG.Spec.X448.P : Nat) =
      ((valN fa 8 * valN fb 8 : Nat) : Int) % (VG.Spec.X448.P : Nat) := by
    rw [key, hP, Int.add_mul_emod_self_left, Nat.cast_mul]
  rw [← Int.natCast_emod, ← Int.natCast_emod] at this
  exact Int.ofNat_inj.mp this

theorem carries_lt {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) :
    cval r 0 7 / 2 ^ 28 < 2 ^ 36 ∧ cval r 8 7 / 2 ^ 28 < 2 ^ 36 :=
  ⟨cin_le (b := 0) (r := r) (fun k hk => hr (0 + k) (by omega_arith)) 8 (by omega_arith),
    cin_le (b := 8) (r := r) (fun k hk => hr (8 + k) (by omega_arith)) 8 (by omega_arith)⟩

theorem limbs28_lt {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) {k : Nat} (hk : k < 16) :
    limbs28 r k < 2 ^ 28 + (if k = 0 then 2 ^ 36 else 0) + (if k = 8 then 2 ^ 37 else 0) := by
  obtain ⟨c7, c15⟩ := carries_lt hr
  have c7' : C7 r < 2 ^ 36 := c7
  have c15' : C15 r < 2 ^ 36 := c15
  unfold limbs28
  split
  · have := Nat.mod_lt (cval r 0 k) (show 2 ^ 28 > 0 by decide)
    split <;> split <;> omega
  · have := Nat.mod_lt (cval r 8 (k - 8)) (show 2 ^ 28 > 0 by decide)
    split <;> split <;> omega_arith

theorem out56_bound {r : Nat → Nat} (hr : ∀ k < 16, r k < 2 ^ 64 - 2 ^ 40) : ∀ i < 8, out56 (limbs28 r) i < Mb := by
  have l : ∀ k < 16, limbs28 r k < 2 ^ 28 + (if k = 0 then 2 ^ 36 else 0) + (if k = 8 then 2 ^ 37 else 0) :=
    fun k hk => limbs28_lt hr hk
  have l0 := l 0 (by decide); have l1 := l 1 (by decide); have l2 := l 2 (by decide); have l3 := l 3 (by decide)
  have l4 := l 4 (by decide); have l5 := l 5 (by decide); have l6 := l 6 (by decide); have l7 := l 7 (by decide)
  have l8 := l 8 (by decide); have l9 := l 9 (by decide); have l10 := l 10 (by decide)
  have l11 := l 11 (by decide); have l12 := l 12 (by decide); have l13 := l 13 (by decide)
  have l14 := l 14 (by decide); have l15 := l 15 (by decide)
  simp at l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15
  have d0 : (limbs28 r 0 + 2 ^ 28 * limbs28 r 1) / 2 ^ 56 < 2 := Nat.div_lt_of_lt_mul (by omega_arith)
  have d4 : (limbs28 r 8 + 2 ^ 28 * limbs28 r 9) / 2 ^ 56 < 2 := Nat.div_lt_of_lt_mul (by omega_arith)
  intro i hi
  simp only [Mb, out56, w56]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega_arith)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [ite_true, ite_false, Nat.mul_zero,
      Nat.zero_add, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd, show (1 : Nat) ≠ 0 by decide,
      show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide,
      show (3 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 4 by decide, show (2 : Nat) ≠ 5 by decide,
      show (3 : Nat) ≠ 4 by decide, show (3 : Nat) ≠ 5 by decide, show (4 : Nat) ≠ 0 by decide, show (4 : Nat) ≠ 1 by decide,
      show (5 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 1 by decide, show (5 : Nat) ≠ 4 by decide,
      show (6 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 1 by decide, show (6 : Nat) ≠ 4 by decide,
      show (6 : Nat) ≠ 5 by decide, show (7 : Nat) ≠ 0 by decide, show (7 : Nat) ≠ 1 by decide,
      show (7 : Nat) ≠ 4 by decide, show (7 : Nat) ≠ 5 by decide] <;>
    first
    | exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    | (simp only [Nat.reducePow] at d0 d4 ⊢; omega_arith)

end VG.Proof.Curve448.AArch64.Neon
