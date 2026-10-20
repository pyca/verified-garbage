module

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Spec.MlKem
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM's 16-bit NTT on AArch64: vectors of halfwords

The halfword lanes (`vhalf`) of the results of the vector instructions of the
16-bit NTT (`Impl/MlKem/AArch64/Ntt16.lean`): the arithmetic on lanes, the
permutations, and the loads and stores.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem

/-! ## Lanes -/

theorem getLsbD_vhalf (x : BitVec 128) (e : Nat) {i : Nat} (hi : i < 16) :
    (vhalf x e).getLsbD i = x.getLsbD (16 * e + i) := by
  simp only [vhalf, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]

theorem vhalf_ext {x y : BitVec 128} (h : ∀ e < 8, vhalf x e = vhalf y e) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (fun w : BitVec 16 => w.getLsbD (i % 16)) (h (i / 16) (by omega))
  simp only [getLsbD_vhalf _ _ (Nat.mod_lt _ (by decide)), show 16 * (i / 16) + i % 16 = i by omega]
    at this
  exact this

theorem vhalf_ofVHalves (f : Nat → BitVec 16) {e : Nat} (he : e < 8) : vhalf (ofVHalves f) e = f e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_vhalf _ _ hi]
  simp only [ofVHalves, BitVec.getLsbD_append]
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp (disch := omega) only [ite_eq_left, ite_eq_right]
    all_goals exact congrArg _ (by omega)

theorem ofVHalves_congr {f g : Nat → BitVec 16} (h : ∀ e < 8, f e = g e) : ofVHalves f = ofVHalves g :=
  vhalf_ext fun e he => by rw [vhalf_ofVHalves _ he, vhalf_ofVHalves _ he, h e he]

theorem ofVHalves_vhalf (x : BitVec 128) : ofVHalves (vhalf x) = x :=
  vhalf_ext fun _ he => vhalf_ofVHalves _ he

theorem vhalf_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat}
    (he : e < 8) : vhalf (VArr.h8.map2 f x y) e = f 16 (vhalf x e) (vhalf y e) := by
  rw [VArr.map2, vhalf_ofVHalves _ he]

/-- Halfword `h` of word `j`. -/
theorem vword_half (x : BitVec 128) (j : Nat) {h : Nat} (hh : h < 2) :
    (vword x j).extractLsb' (16 * h) 16 = vhalf x (2 * j + h) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, getLsbD_vhalf _ _ hi,
    show 16 * h + i < 32 by omega]
  exact congrArg _ (by omega)

theorem vword_lo (x : BitVec 128) (j : Nat) : (vword x j).extractLsb' 0 16 = vhalf x (2 * j) :=
  vword_half x j (h := 0) (by decide)

theorem vword_hi (x : BitVec 128) (j : Nat) : (vword x j).extractLsb' 16 16 = vhalf x (2 * j + 1) :=
  vword_half x j (h := 1) (by decide)

/-- Halfword `h` of doubleword `j`. -/
theorem vdword_half (x : BitVec 128) (j : Nat) {h : Nat} (hh : h < 4) :
    (vdword x j).extractLsb' (16 * h) 16 = vhalf x (4 * j + h) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, getLsbD_vhalf _ _ hi,
    show 16 * h + i < 64 by omega]
  exact congrArg _ (by omega)

theorem vhalf_ofVWords (w0 w1 w2 w3 : BitVec 32) {e : Nat} (he : e < 8) :
    vhalf (ofVWords w0 w1 w2 w3) e = ([w0, w1, w2, w3][e / 2]'(by simp; omega)).extractLsb' (16 * (e % 2)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_vhalf _ _ hi]
  simp only [ofVWords, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp (disch := omega) only [Nat.mul_zero, Nat.zero_add, Nat.reduceMul, Nat.reduceDiv,
      Nat.reduceMod, List.getElem_cons_zero, List.getElem_cons_succ, ite_eq_left, ite_eq_right]
    all_goals exact congrArg _ (by omega)

theorem vhalf_ofVDwords (d0 d1 : BitVec 64) {e : Nat} (he : e < 8) :
    vhalf (ofVDwords d0 d1) e = (if e < 4 then d0 else d1).extractLsb' (16 * (e % 4)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_vhalf _ _ hi]
  simp only [ofVDwords, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and]
  by_cases h : e < 4
  · rw [ite_eq_left (show 16 * e + i < 64 by omega), ite_eq_left h]; exact congrArg _ (by omega)
  · rw [ite_eq_right (show ¬ 16 * e + i < 64 by omega), ite_eq_right h]; exact congrArg _ (by omega)

/-! ## Permutations -/

private theorem range2 : List.range 2 = [0, 1] := rfl

private theorem range4 : List.range 4 = [0, 1, 2, 3] := rfl

private theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

private theorem sw16 (w : BitVec 16) : (w.setWidth 128).setWidth 16 = w := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- A permutation of halfwords, as the sources of its lanes. -/
theorem vhalf_perm_h8 (op : VPermOp) (x y : BitVec 128) {e : Nat} (he : e < 8) :
    vhalf (op.eval .h8 x y) e =
      match op with
      | .zip1 => if e % 2 = 0 then vhalf x (e / 2) else vhalf y (e / 2)
      | .zip2 => if e % 2 = 0 then vhalf x (4 + e / 2) else vhalf y (4 + e / 2)
      | .trn1 => if e % 2 = 0 then vhalf x e else vhalf y (e - 1)
      | .trn2 => if e % 2 = 0 then vhalf x (e + 1) else vhalf y e
      | .uzp1 => if e < 4 then vhalf x (2 * e) else vhalf y (2 * e - 8)
      | .uzp2 => if e < 4 then vhalf x (2 * e + 1) else vhalf y (2 * e - 7) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_map, List.length_range]
  rw [vhalf_ofVHalves _ he]
  cases op <;>
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [range4, range8]

/-- A permutation of words, as the sources of its halfwords. -/
theorem vhalf_perm_s4 (op : VPermOp) (x y : BitVec 128) {e : Nat} (he : e < 8) :
    vhalf (op.eval .s4 x y) e =
      match op with
      | .zip1 => if e / 2 % 2 = 0 then vhalf x (e / 4 * 2 + e % 2) else vhalf y (e / 4 * 2 + e % 2)
      | .zip2 => if e / 2 % 2 = 0 then vhalf x (4 + e / 4 * 2 + e % 2)
          else vhalf y (4 + e / 4 * 2 + e % 2)
      | .trn1 => if e / 2 % 2 = 0 then vhalf x e else vhalf y (e - 2)
      | .trn2 => if e / 2 % 2 = 0 then vhalf x (e + 2) else vhalf y e
      | .uzp1 => if e < 4 then vhalf x (2 * (e / 2) * 2 + e % 2) else vhalf y (2 * (e / 2) * 2 + e % 2 - 8)
      | .uzp2 => if e < 4 then vhalf x (2 * (e / 2) * 2 + 2 + e % 2)
          else vhalf y (2 * (e / 2) * 2 + e % 2 - 6) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceDiv]
  rw [vhalf_ofVWords _ _ _ _ he]
  cases op <;>
  match e, he with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [range2, range4, vword_lo, vword_hi]

private theorem eval_trn_d2 (x y : BitVec 128) :
    VPermOp.eval .trn1 .d2 x y = ofVDwords (vdword x 0) (vdword y 0) ∧
    VPermOp.eval .trn2 .d2 x y = ofVDwords (vdword x 1) (vdword y 1) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceDiv]
  exact ⟨by rw [show (List.range 1) = [0] from rfl]; simp,
    by rw [show (List.range 1) = [0] from rfl]; simp⟩

/-- A permutation of doublewords, as the sources of its halfwords. -/
theorem vhalf_trn_d2 (x y : BitVec 128) {e : Nat} (he : e < 8) :
    vhalf (VPermOp.eval .trn1 .d2 x y) e = (if e < 4 then vhalf x e else vhalf y (e - 4)) ∧
    vhalf (VPermOp.eval .trn2 .d2 x y) e = (if e < 4 then vhalf x (e + 4) else vhalf y e) := by
  rw [(eval_trn_d2 x y).1, (eval_trn_d2 x y).2, vhalf_ofVDwords _ _ he, vhalf_ofVDwords _ _ he]
  by_cases h : e < 4
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, ite_eq_left h, vdword_half _ _ (by omega),
      vdword_half _ _ (by omega)]
    exact ⟨congrArg _ (by omega), congrArg _ (by omega)⟩
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, ite_eq_right h, vdword_half _ _ (by omega),
      vdword_half _ _ (by omega)]
    exact ⟨congrArg _ (by omega), congrArg _ (by omega)⟩

/-! ## Lanes modulo `q` -/

/-- A lane `a` represents `X` with the bound `B`: `|a| < B` and `a ≡ X (mod q)`. -/
def LRep (a : BitVec 16) (X : Zq) (B : Nat) : Prop :=
  -(B : Int) < a.toInt ∧ a.toInt < B ∧ (a.toInt - (X.val : Int)) % 3329 = 0

/-- The lanes of `x` represent `g` with the bound `B`. -/
def Rep (x : BitVec 128) (g : Nat → Zq) (B : Nat) : Prop := ∀ e < 8, LRep (vhalf x e) (g e) B

/-- The lanes of `x` are the constants `c`. -/
def Cst (x : BitVec 128) (c : Nat → Nat) : Prop := ∀ e < 8, vhalf x e = BitVec.ofNat 16 (c e)

theorem LRep.mono {a : BitVec 16} {X : Zq} {B B' : Nat} (h : LRep a X B) (hB : B ≤ B') : LRep a X B' :=
  ⟨by have := h.1; omega, by have := h.2.1; omega, h.2.2⟩

theorem Rep.mono {x : BitVec 128} {g : Nat → Zq} {B B' : Nat} (h : Rep x g B) (hB : B ≤ B') : Rep x g B' :=
  fun e he => (h e he).mono hB

theorem Rep.congr {x : BitVec 128} {g g' : Nat → Zq} {B : Nat} (h : Rep x g B) (hg : ∀ e < 8, g e = g' e) :
    Rep x g' B := fun e he => by rw [← hg e he]; exact h e he

private theorem toInt_add16 {a r : BitVec 16} (h1 : -32768 ≤ a.toInt + r.toInt)
    (h2 : a.toInt + r.toInt < 32768) : (a + r).toInt = a.toInt + r.toInt := by
  rw [BitVec.toInt_add]; simp only [Int.bmod_def]; split <;> omega

private theorem toInt_sub16 {a r : BitVec 16} (h1 : -32768 ≤ a.toInt - r.toInt)
    (h2 : a.toInt - r.toInt < 32768) : (a - r).toInt = a.toInt - r.toInt := by
  rw [BitVec.toInt_sub]; simp only [Int.bmod_def]; split <;> omega

private theorem toInt_ofNat16 {z : Nat} (hz : z < 32768) : (BitVec.ofNat 16 z).toInt = z := by
  rw [BitVec.toInt_ofNat']; simp only [Int.bmod_def]; omega

/-- A butterfly on one lane: `a ± r`, `r = b · z - t · q`, `t = sqrdmulh(b, tw z)`. -/
theorem bf_lane {a b : BitVec 16} {X Y : Zq} {z Bx By : Nat} (ha : LRep a X Bx) (hb : LRep b Y By)
    (hz : z < 3329) (hB : Bx + 3329 ≤ 32768) (hBy : By ≤ 32768) :
    ∃ t, sqdmulhHLane true b (BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.tw z)) = some t ∧
      LRep (a + (b * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329)) (X + ofNat z * Y) (Bx + 3329) ∧
      LRep (a - (b * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329)) (X - ofNat z * Y) (Bx + 3329) := by
  obtain ⟨t, ht, h1, h2, h3⟩ := mm_ok b (z := z) (by have := hb.1; omega) hz
  refine ⟨t, ht, ?_⟩
  generalize b * BitVec.ofNat 16 z - t * BitVec.ofNat 16 3329 = r at h1 h2 h3
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨-, -, b3⟩ := hb
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero b3
  have hbz : b.toInt * z = (Y.val : Int) * z + 3329 * (k * z) := by
    rw [show b.toInt = Y.val + 3329 * k by omega]; grind
  have e2 : (ofNat z * Y).val = z * Y.val % 3329 := by
    rw [val_mul, val_ofNat, Nat.mod_eq_of_lt (show z < q from hz)]
  have e1 : (X + ofNat z * Y).val = (X.val + z * Y.val % 3329) % 3329 := by rw [val_add', e2]
  have e3 : (X - ofNat z * Y).val = (X.val + (3329 - z * Y.val % 3329)) % 3329 := by
    rw [val_sub', e2]
  have hY := val_lt Y
  have hX := val_lt X
  have hW : ((z * Y.val : Nat) : Int) = (Y.val : Int) * z := by
    rw [Int.natCast_mul, Int.mul_comm]
  generalize z * Y.val = W at e1 e3 hW
  generalize (Y.val : Int) * z = Wi at hbz hW
  simp only [LRep, toInt_add16 (a := a) (r := r) (by omega) (by omega),
    toInt_sub16 (a := a) (r := r) (by omega) (by omega), e1, e3]
  omega

/-! ## Instructions -/

/-- A product of halfwords, all of whose lanes are defined. -/
theorem eval_mulH {s : State} {op : VMulHOp} {d n m : VReg}
    (h : ∀ e < 8, (op.lane (vhalf (s.v d) e) (vhalf (s.v n) e) (vhalf (s.v m) e)).isSome) :
    VOp.eval s (.mulH op d n m) =
      some (d, ofVHalves fun e => (op.lane (vhalf (s.v d) e) (vhalf (s.v n) e) (vhalf (s.v m) e)).getD 0) := by
  simp only [VOp.eval]
  rw [ite_eq_left (by
    rw [range8]
    simp only [List.all_cons, List.all_nil, h 0 (by decide), h 1 (by decide), h 2 (by decide),
      h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide),
      Bool.and_self])]

theorem vhalf_mulH {s : State} {op : VMulHOp} {d n m : VReg} {e : Nat} (he : e < 8) {r : BitVec 16}
    (hr : op.lane (vhalf (s.v d) e) (vhalf (s.v n) e) (vhalf (s.v m) e) = some r) :
    vhalf (ofVHalves fun e => (op.lane (vhalf (s.v d) e) (vhalf (s.v n) e) (vhalf (s.v m) e)).getD 0) e = r := by
  rw [vhalf_ofVHalves _ he, hr]; rfl

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

open Impl.MlKem.AArch64.Ntt16 in
/-- The butterflies on the lanes of `x` and `y` with the zetas `Z` (in `z`, their
`tw` in `t`, `q` in `v31`): `x ← x + Z·y`, `y ← x - Z·y` modulo `q`. -/
theorem bf_ok {x y z t : VReg} (hxy : x ≠ y := by decide) (hx16 : x ≠ .v16 := by decide)
    (hx17 : x ≠ .v17 := by decide) (hy16 : y ≠ .v16 := by decide)
    (ht16 : t ≠ .v16 := by decide) {X Y : Nat → Zq} {Z : Nat → Nat} {Bx By : Nat}
    (hx : Rep (s.v x) X Bx) (hy : Rep (s.v y) Y By) (hz : Cst (s.v z) Z)
    (ht : Cst (s.v t) fun e => tw (Z e)) (hq : Cst (s.v .v31) fun _ => 3329) (hZ : ∀ e < 8, Z e < 3329)
    (hB : Bx + 3329 ≤ 32768) (hBy : By ≤ 32768)
    (k : ∀ s', VChg [.v16, .v17, .v16, y, x] s s' →
      Rep (s'.v x) (fun e => X e + ofNat (Z e) * Y e) (Bx + 3329) →
      Rep (s'.v y) (fun e => X e - ofNat (Z e) * Y e) (Bx + 3329) → WP isa (.block rest) s' Q) :
    WP isa (.block (bf x y z t ++ rest)) s Q := by
  simp only [bf, List.cons_append, List.nil_append]
  refine wp_vop (eval_mulH fun _ _ => rfl) fun s₁ h₁ => ?_
  have L : ∀ e < 8, ∃ T, sqdmulhHLane true (vhalf (s.v y) e) (BitVec.ofNat 16 (tw (Z e))) = some T ∧
      LRep (vhalf (s.v x) e + (vhalf (s.v y) e * BitVec.ofNat 16 (Z e) - T * BitVec.ofNat 16 3329))
        (X e + ofNat (Z e) * Y e) (Bx + 3329) ∧
      LRep (vhalf (s.v x) e - (vhalf (s.v y) e * BitVec.ofNat 16 (Z e) - T * BitVec.ofNat 16 3329))
        (X e - ofNat (Z e) * Y e) (Bx + 3329) := fun e he =>
    bf_lane (hx e he) (hy e he) (hZ e he) hB hBy
  have y₁ : s₁.v y = s.v y := h₁.get y hy16
  have t₁ : s₁.v t = s.v t := h₁.get t ht16
  refine wp_vop (eval_mulH fun e he => by
    obtain ⟨T, hT, -⟩ := L e he
    simp only [VMulHOp.lane, y₁, t₁, ht e he, hT, Option.isSome_some]) fun s₂ h₂ => ?_
  refine wp_vop (eval_mulH fun _ _ => rfl) fun s₃ h₃ => ?_
  refine wp_vop rfl fun s₄ h₄ => wp_vop rfl fun s₅ h₅ => ?_
  have c : VChg [.v16, .v17, .v16, y, x] s s₅ :=
    (((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans h₅.chg
  -- the lanes of `v16` after `mls`
  have r16 : ∀ e < 8, ∃ T, sqdmulhHLane true (vhalf (s.v y) e) (BitVec.ofNat 16 (tw (Z e))) = some T ∧
      vhalf (s₃.v .v16) e = vhalf (s.v y) e * BitVec.ofNat 16 (Z e) - T * BitVec.ofNat 16 3329 := by
    intro e he
    obtain ⟨T, hT, -⟩ := L e he
    refine ⟨T, hT, ?_⟩
    have q₂ : s₂.v .v31 = s.v .v31 := by rw [h₂.get .v31, h₁.get .v31]
    have v₂ : s₂.v .v16 = s₁.v .v16 := h₂.get .v16
    rw [h₃.v, vhalf_mulH he (r := vhalf (s.v y) e * BitVec.ofNat 16 (Z e) - T * BitVec.ofNat 16 3329)]
    rw [h₂.v, q₂, v₂, h₁.v, vhalf_ofVHalves _ he, vhalf_ofVHalves _ he]
    simp only [VMulHOp.lane, y₁, t₁, ht e he, hT, Option.getD_some, hq e he, hz e he]
  refine k s₅ c (fun e he => ?_) (fun e he => ?_)
  · obtain ⟨T, hT, h16⟩ := r16 e he
    obtain ⟨T', hT', l1, -⟩ := L e he
    rw [hT] at hT'; cases hT'
    rw [h₅.v, vhalf_map2 _ _ _ he, h₄.get x hxy, h₄.get .v16 (Ne.symm hy16), h₃.get x hx16,
      h₂.get x hx17, h₁.get x hx16, h16]
    exact l1
  · obtain ⟨T, hT, h16⟩ := r16 e he
    obtain ⟨T', hT', -, l2⟩ := L e he
    rw [hT] at hT'; cases hT'
    rw [h₅.get y (Ne.symm hxy), h₄.v, vhalf_map2 _ _ _ he, h₃.get x hx16, h₂.get x hx17,
      h₁.get x hx16, h16]
    exact l2

end

end VG.Proof.MlKem.AArch64.Ntt16
