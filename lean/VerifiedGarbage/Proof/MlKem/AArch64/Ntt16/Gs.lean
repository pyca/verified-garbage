module
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Idx
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM's 16-bit inverse NTT on AArch64: lanes

The inverse butterfly `gs x y z t` (`Impl/MlKem/AArch64/Ntt16.lean`):
`x ← x + y`, `y ← (y - x) · z mod q` (`gs_lane`, `gs_ok`), and a reduction
of the lanes to less than `q` in absolute value (`reduce_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

private theorem toInt_add16' {a r : BitVec 16} (h1 : -32768 ≤ a.toInt + r.toInt)
    (h2 : a.toInt + r.toInt < 32768) : (a + r).toInt = a.toInt + r.toInt := by
  rw [BitVec.toInt_add]; simp only [Int.bmod_def]; split <;> omega

private theorem toInt_sub16' {a r : BitVec 16} (h1 : -32768 ≤ a.toInt - r.toInt)
    (h2 : a.toInt - r.toInt < 32768) : (a - r).toInt = a.toInt - r.toInt := by
  rw [BitVec.toInt_sub]; simp only [Int.bmod_def]; split <;> omega

/-- An inverse butterfly on one lane: `a + b`, and `r = d · z - t · q` for
`d = b - a`, `t = sqrdmulh(d, tw z)`. -/
theorem gs_lane {a b : BitVec 16} {X Y : Zq} {z Bx By : Nat} (ha : LRep a X Bx) (hb : LRep b Y By)
    (hz : z < 3329) (hB : Bx + By ≤ 32768) :
    ∃ t, sqdmulhHLane true (b - a) (BitVec.ofNat 16 (tw z)) = some t ∧
      LRep (a + b) (X + Y) (Bx + By) ∧
      LRep ((b - a) * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329) (ofNat z * (Y - X)) 3329 := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  have hd : (b - a).toInt = b.toInt - a.toInt := toInt_sub16' (by omega) (by omega)
  obtain ⟨t, ht, h1, h2, h3⟩ := mm_ok (b - a) (z := z) (by omega) hz
  refine ⟨t, ht, ?_, ?_⟩
  · have hX := val_lt X
    have hY := val_lt Y
    have e1 : (X + Y).val = (X.val + Y.val) % 3329 := val_add' X Y
    refine ⟨?_, ?_, ?_⟩ <;> rw [toInt_add16' (by omega) (by omega)] <;> [omega; omega; skip]
    rw [e1]; omega
  · refine ⟨h1, h2, ?_⟩
    rw [hd] at h3
    generalize (b - a) * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329 = r at h1 h2 h3 ⊢
    obtain ⟨k1, hk1⟩ := Int.dvd_of_emod_eq_zero b3
    obtain ⟨k2, hk2⟩ := Int.dvd_of_emod_eq_zero a3
    have hX := val_lt X
    have hY := val_lt Y
    -- `(Y - X).val = Y - X + q·c`
    have eD : ((Y - X).val : Int) = (Y.val : Int) - X.val + 3329 * (if X.val ≤ Y.val then 0 else 1) := by
      rw [val_sub_eq]
      have hq : q = 3329 := rfl
      by_cases h : X.val ≤ Y.val <;> simp only [h, ite_true, ite_false] <;> omega
    have e2 : (ofNat z * (Y - X)).val = z * (Y - X).val % 3329 := by
      rw [val_mul, val_ofNat, Nat.mod_eq_of_lt (show z < q from hz)]
    rw [e2]
    have hm : (b.toInt - a.toInt) * z =
        (((Y - X).val : Int) * z) + 3329 * ((k1 - k2 - (if X.val ≤ Y.val then 0 else 1)) * z) := by
      rw [eD, show b.toInt = Y.val + 3329 * k1 by omega, show a.toInt = X.val + 3329 * k2 by omega]
      split <;> grind
    have hW : ((z * (Y - X).val : Nat) : Int) = ((Y - X).val : Int) * z := by
      rw [Int.natCast_mul, Int.mul_comm]
    rw [hm] at h3
    generalize z * (Y - X).val = W at hW ⊢
    generalize ((Y - X).val : Int) * z = Wi at hW h3
    generalize (k1 - k2 - (if X.val ≤ Y.val then 0 else 1)) * (z : Int) = K at h3
    omega

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- The inverse butterflies on the lanes of `x` and `y` with the zetas `Z` (in `z`, their `tw`
in `t`): `x ← x + y`, `y ← Z·(y - x)` modulo `q`. -/
theorem gs_ok {x y z t : VReg} (hxy : x ≠ y := by decide) (hx17 : x ≠ .v17 := by decide)
    (hy17 : y ≠ .v17 := by decide) (hzx : z ≠ x := by decide) (hz17 : z ≠ .v17 := by decide)
    (htx : t ≠ x := by decide) (hty : t ≠ y := by decide) (ht17 : t ≠ .v17 := by decide)
    (hqx : VReg.v31 ≠ x := by decide) (hqy : VReg.v31 ≠ y := by decide)
    {X Y : Nat → Zq} {Z : Nat → Nat} {Bx By : Nat}
    (hx : Rep (s.v x) X Bx) (hy : Rep (s.v y) Y By) (hz : Cst (s.v z) Z)
    (ht : Cst (s.v t) fun e => tw (Z e)) (hq : Cst (s.v .v31) fun _ => 3329) (hZ : ∀ e < 8, Z e < 3329)
    (hB : Bx + By ≤ 32768)
    (k : ∀ s', VChg [.v17, x, y, .v17, y] s s' →
      Rep (s'.v x) (fun e => X e + Y e) (Bx + By) →
      Rep (s'.v y) (fun e => ofNat (Z e) * (Y e - X e)) 3329 → WP isa (.block rest) s' Q) :
    WP isa (.block (gs x y z t ++ rest)) s Q := by
  simp only [gs, List.cons_append, List.nil_append]
  have L : ∀ e < 8, ∃ T, sqdmulhHLane true (vhalf (s.v y) e - vhalf (s.v x) e)
      (BitVec.ofNat 16 (tw (Z e))) = some T ∧
      LRep (vhalf (s.v x) e + vhalf (s.v y) e) (X e + Y e) (Bx + By) ∧
      LRep ((vhalf (s.v y) e - vhalf (s.v x) e) * BitVec.ofNat 16 (Z e) - T * BitVec.ofNat 16 3329)
        (ofNat (Z e) * (Y e - X e)) 3329 := fun e he =>
    gs_lane (hx e he) (hy e he) (hZ e he) hB
  refine wp_vop rfl fun s₁ h₁ => wp_vop rfl fun s₂ h₂ => ?_
  have d₂ : ∀ e < 8, vhalf (s₂.v .v17) e = vhalf (s.v y) e - vhalf (s.v x) e := fun e he => by
    rw [h₂.get .v17 (Ne.symm hx17), h₁.v, vhalf_map2 _ _ _ he]
  refine wp_vop (eval_mulH fun _ _ => rfl) fun s₃ h₃ => ?_
  refine wp_vop (eval_mulH fun e he => by
    obtain ⟨T, hT, -⟩ := L e he
    simp only [VMulHOp.lane, h₃.get .v17 (Ne.symm hy17), d₂ e he, h₃.get t hty, h₂.get t htx,
      h₁.get t ht17, ht e he, hT, Option.isSome_some]) fun s₄ h₄ => ?_
  refine wp_vop (eval_mulH fun _ _ => rfl) fun s₅ h₅ => ?_
  refine k s₅ ((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans h₅.chg) (fun e he => ?_)
    (fun e he => ?_)
  · obtain ⟨T, hT, l1, -⟩ := L e he
    rw [h₅.get x hxy, h₄.get x hx17, h₃.get x hxy, h₂.v, vhalf_map2 _ _ _ he,
      h₁.get x hx17, h₁.get y hy17]
    exact l1
  · obtain ⟨T, hT, -, l2⟩ := L e he
    have v17 : vhalf (s₄.v .v17) e = T := by
      rw [h₄.v, vhalf_ofVHalves _ he]
      simp only [VMulHOp.lane, h₃.get .v17 (Ne.symm hy17), d₂ e he, h₃.get t hty, h₂.get t htx,
        h₁.get t ht17, ht e he, hT, Option.getD_some]
    have y₄ : vhalf (s₄.v y) e = (vhalf (s.v y) e - vhalf (s.v x) e) * BitVec.ofNat 16 (Z e) := by
      rw [h₄.get y hy17, h₃.v, vhalf_ofVHalves _ he]
      simp only [VMulHOp.lane, Option.getD_some, d₂ e he, h₂.get z hzx, h₁.get z hz17, hz e he]
    rw [h₅.v, vhalf_ofVHalves _ he]
    simp only [VMulHOp.lane, Option.getD_some, y₄, v17, h₄.get .v31, h₃.get .v31 hqy, h₂.get .v31 hqx,
      h₁.get .v31, hq e he]
    exact l2

/-- `reduce x`: the lanes of `x`, less than `2¹⁵` in absolute value, reduced to less than `q`. -/
theorem reduce_ok {x : VReg} (h16 : x ≠ .v16 := by decide) {X : Nat → Zq} {B : Nat}
    (hx : Rep (s.v x) X B) (hB : B ≤ 32768) (h10 : Cst (s.v .v30) fun _ => 10)
    (hq : Cst (s.v .v31) fun _ => 3329)
    (k : ∀ s', VChg [.v16, x] s s' → Rep (s'.v x) X 3329 → WP isa (.block rest) s' Q) :
    WP isa (.block (reduce x ++ rest)) s Q := by
  simp only [reduce, List.cons_append, List.nil_append]
  have L : ∀ e < 8, ∃ T, sqdmulhHLane true (vhalf (s.v x) e) (BitVec.ofNat 16 10) = some T ∧
      LRep (vhalf (s.v x) e - T * BitVec.ofNat 16 3329) (X e) 3329 := by
    intro e he
    obtain ⟨a1, a2, a3⟩ := hx e he
    obtain ⟨T, hT, b1, b2, b3⟩ := mm_ok (vhalf (s.v x) e) (z := 1) (by omega) (by decide)
    rw [tw_one, show (vhalf (s.v x) e) * BitVec.ofNat 16 1 = vhalf (s.v x) e from BitVec.mul_one _]
      at *
    exact ⟨T, hT, b1, b2, by omega⟩
  refine wp_vop (eval_mulH fun e he => by
    obtain ⟨T, hT, -⟩ := L e he
    simp only [VMulHOp.lane, h10 e he, hT, Option.isSome_some]) fun s₁ h₁ => ?_
  refine wp_vop (eval_mulH fun _ _ => rfl) fun s₂ h₂ => k s₂ (h₁.chg.trans h₂.chg) fun e he => ?_
  obtain ⟨T, hT, l⟩ := L e he
  rw [h₂.v, vhalf_ofVHalves _ he]
  simp only [VMulHOp.lane, h₁.v, h₁.get x h16, h₁.get .v31, vhalf_ofVHalves _ he, h10 e he, hT,
    Option.getD_some, hq e he]
  exact l

end

end VG.Proof.MlKem.AArch64.Ntt16
