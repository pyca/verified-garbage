module

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Rows
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.NttLayer
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM's 16-bit NTT on AArch64: lanes by index

Pass 2 of the 16-bit NTT permutes the 32 coefficients of a block among its
registers. A register holds, in lane `e`, the coefficient `base + o[e]` of
the polynomial after `j` layers (`IRep`), for a list of offsets `o`; its
zetas are `zeta (K₀ + kz[e])` (`ZRep`, their `tw`: `TRep`). A permutation
maps the lists (`irep_perm`, `zrep_perm`, which `decide` checks), and a
butterfly advances a layer when its offsets are those of the layer's pairs
(`okBf`, `irep_bf`). `norm_ok`: a lane reduced to `[0, q)`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-- Lane `e` of `x` is coefficient `base + o[e]` of `P` after `j` layers. -/
def IRep (P : Poly) (j base : Nat) (o : List Nat) (x : BitVec 128) : Prop :=
  Rep x (fun e => (nttL j P)[base + o.getD e 0]!) ((j + 1) * 3329)

/-- Lane `e` of `x` is `zeta (K₀ + kz[e])`. -/
def ZRep (x : BitVec 128) (K₀ : Nat) (kz : List Nat) : Prop :=
  Cst x fun e => Impl.MlKem.AArch64.Ntt16.zeta (K₀ + kz.getD e 0)

/-- Lane `e` of `x` is `tw (zeta (K₀ + kz[e]))`. -/
def TRep (x : BitVec 128) (K₀ : Nat) (kz : List Nat) : Prop :=
  Cst x fun e => tw (Impl.MlKem.AArch64.Ntt16.zeta (K₀ + kz.getD e 0))

/-! ## Permutations -/

/-- The lanes of `r` taken from `x` or `y`. -/
def Src (r x y : BitVec 128) (c : Nat → Bool) (i₁ i₂ : Nat → Nat) : Prop :=
  ∀ e < 8, vhalf r e = if c e then vhalf x (i₁ e) else vhalf y (i₂ e)

/-- The offsets after a permutation. -/
def permO (ox oy : List Nat) (c : Nat → Bool) (i₁ i₂ : Nat → Nat) (o : List Nat) : Bool :=
  (List.range 8).all fun e => o.getD e 0 == if c e then ox.getD (i₁ e) 0 else oy.getD (i₂ e) 0

theorem irep_perm {P : Poly} {j base : Nat} {ox oy o : List Nat} {r x y : BitVec 128} {c : Nat → Bool}
    {i₁ i₂ : Nat → Nat} (hs : Src r x y c i₁ i₂) (hi : ∀ e < 8, (if c e then i₁ e else i₂ e) < 8)
    (hx : IRep P j base ox x) (hy : IRep P j base oy y) (ho : permO ox oy c i₁ i₂ o = true) :
    IRep P j base o r := fun e he => by
  simp only [permO, List.all_eq_true, List.mem_range, beq_iff_eq] at ho
  dsimp only
  rw [hs e he, ho e he]
  have hi' := hi e he
  by_cases h : c e
  · simp only [h, ite_true] at hi' ⊢; exact hx _ hi'
  · simp only [h, ite_false, Bool.false_eq_true] at hi' ⊢; exact hy _ hi'

theorem zrep_perm {K₀ : Nat} {kx ky k : List Nat} {r x y : BitVec 128} {c : Nat → Bool}
    {i₁ i₂ : Nat → Nat} (hs : Src r x y c i₁ i₂) (hi : ∀ e < 8, (if c e then i₁ e else i₂ e) < 8)
    (hx : ZRep x K₀ kx) (hy : ZRep y K₀ ky) (ho : permO kx ky c i₁ i₂ k = true) :
    ZRep r K₀ k := fun e he => by
  simp only [permO, List.all_eq_true, List.mem_range, beq_iff_eq] at ho
  dsimp only
  rw [hs e he, ho e he]
  have hi' := hi e he
  by_cases h : c e
  · simp only [h, ite_true] at hi' ⊢; exact hx _ hi'
  · simp only [h, ite_false, Bool.false_eq_true] at hi' ⊢; exact hy _ hi'

theorem trep_perm {K₀ : Nat} {kx ky k : List Nat} {r x y : BitVec 128} {c : Nat → Bool}
    {i₁ i₂ : Nat → Nat} (hs : Src r x y c i₁ i₂) (hi : ∀ e < 8, (if c e then i₁ e else i₂ e) < 8)
    (hx : TRep x K₀ kx) (hy : TRep y K₀ ky) (ho : permO kx ky c i₁ i₂ k = true) :
    TRep r K₀ k := fun e he => by
  simp only [permO, List.all_eq_true, List.mem_range, beq_iff_eq] at ho
  dsimp only
  rw [hs e he, ho e he]
  have hi' := hi e he
  by_cases h : c e
  · simp only [h, ite_true] at hi' ⊢; exact hx _ hi'
  · simp only [h, ite_false, Bool.false_eq_true] at hi' ⊢; exact hy _ hi'

theorem src_h8 (op : VPermOp) (x y : BitVec 128) :
    Src (op.eval .h8 x y) x y
      (match op with
        | .zip1 | .zip2 | .trn1 | .trn2 => fun e => e % 2 == 0
        | .uzp1 | .uzp2 => fun e => decide (e < 4))
      (match op with
        | .zip1 => fun e => e / 2 | .zip2 => fun e => 4 + e / 2 | .trn1 => fun e => e
        | .trn2 => fun e => e + 1 | .uzp1 => fun e => 2 * e | .uzp2 => fun e => 2 * e + 1)
      (match op with
        | .zip1 => fun e => e / 2 | .zip2 => fun e => 4 + e / 2 | .trn1 => fun e => e - 1
        | .trn2 => fun e => e | .uzp1 => fun e => 2 * e - 8 | .uzp2 => fun e => 2 * e - 7) :=
  fun e he => by
    rw [vhalf_perm_h8 _ _ _ he]
    cases op <;> simp only [beq_iff_eq, decide_eq_true_eq]

theorem src_s4 (op : VPermOp) (x y : BitVec 128) :
    Src (op.eval .s4 x y) x y
      (match op with
        | .zip1 | .zip2 | .trn1 | .trn2 => fun e => e / 2 % 2 == 0
        | .uzp1 | .uzp2 => fun e => decide (e < 4))
      (match op with
        | .zip1 => fun e => e / 4 * 2 + e % 2 | .zip2 => fun e => 4 + e / 4 * 2 + e % 2
        | .trn1 => fun e => e | .trn2 => fun e => e + 2
        | .uzp1 => fun e => 2 * (e / 2) * 2 + e % 2 | .uzp2 => fun e => 2 * (e / 2) * 2 + 2 + e % 2)
      (match op with
        | .zip1 => fun e => e / 4 * 2 + e % 2 | .zip2 => fun e => 4 + e / 4 * 2 + e % 2
        | .trn1 => fun e => e - 2 | .trn2 => fun e => e
        | .uzp1 => fun e => 2 * (e / 2) * 2 + e % 2 - 8
        | .uzp2 => fun e => 2 * (e / 2) * 2 + e % 2 - 6) :=
  fun e he => by
    rw [vhalf_perm_s4 _ _ _ he]
    cases op <;> simp only [beq_iff_eq, decide_eq_true_eq]

theorem src_trn1_d2 (x y : BitVec 128) :
    Src (VPermOp.eval .trn1 .d2 x y) x y (fun e => decide (e < 4)) (fun e => e) (fun e => e - 4) :=
  fun e he => by rw [(vhalf_trn_d2 x y he).1]; simp only [decide_eq_true_eq]

theorem src_trn2_d2 (x y : BitVec 128) :
    Src (VPermOp.eval .trn2 .d2 x y) x y (fun e => decide (e < 4)) (fun e => e + 4) (fun e => e) :=
  fun e he => by rw [(vhalf_trn_d2 x y he).2]; simp only [decide_eq_true_eq]

/-! ## Butterflies -/

/-- The lanes `ox`, `oy` are the pairs of butterflies of layer `j + 1` (`len = 128 >>> j`), in a
block of 32 coefficients from a multiple of 32, with zetas `zeta (K₀ + kz[e])`. -/
def okBf (j : Nat) (ox oy kz : List Nat) : Bool :=
  let len := 128 >>> j
  j < 7 && 32 % (2 * len) == 0 && (List.range 8).all fun e =>
    ox.getD e 0 < 32 && oy.getD e 0 < 32 && decide (ox.getD e 0 % (2 * len) < len) &&
      oy.getD e 0 == ox.getD e 0 + len && kz.getD e 0 == ox.getD e 0 / (2 * len)

private theorem mod_div_base {d base o : Nat} (hd : 0 < d) (h : base % d = 0) :
    (base + o) % d = o % d ∧ (base + o) / d = base / d + o / d := by
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  exact ⟨by rw [Nat.mul_add_mod], by rw [Nat.mul_add_div hd, Nat.mul_div_cancel_left _ hd]⟩

private theorem zeta_idx_lt : ∀ j < 7, ∀ i < 256, 128 / (128 >>> j) + i / (2 * (128 >>> j)) < 128 := by
  intro j hj i hi
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => simp only [Nat.reduceShiftRight]; omega_arith

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- The butterflies on `x` and `y` with the zetas in `z` (their `tw` in `t`). -/
theorem irep_bf {x y z t : VReg} (hxy : x ≠ y := by decide) (hx16 : x ≠ .v16 := by decide)
    (hx17 : x ≠ .v17 := by decide) (hy16 : y ≠ .v16 := by decide) (ht16 : t ≠ .v16 := by decide)
    {P : Poly} {j base K₀ : Nat} {ox oy kz : List Nat} (hok : okBf j ox oy kz = true)
    (hb : base % 32 = 0) (hb' : base + 32 ≤ 256)
    (hK : K₀ = 128 / (128 >>> j) + base / (2 * (128 >>> j)))
    (hx : IRep P j base ox (s.v x)) (hy : IRep P j base oy (s.v y))
    (hz : ZRep (s.v z) K₀ kz) (ht : TRep (s.v t) K₀ kz) (hq : Cst (s.v .v31) fun _ => 3329)
    (k : ∀ s', VChg [.v16, .v17, .v16, y, x] s s' → IRep P (j + 1) base ox (s'.v x) →
      IRep P (j + 1) base oy (s'.v y) → WP isa (.block rest) s' Q) :
    WP isa (.block (bf x y z t ++ rest)) s Q := by
  simp only [okBf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, and_assoc] at hok
  obtain ⟨hj, h32, hl⟩ := hok
  have hlen : 0 < 128 >>> j := (by decide : ∀ j < 7, 0 < 128 >>> j) j hj
  generalize hL : 128 >>> j = len at hl h32 hK hlen
  have hbd : base % (2 * len) = 0 := by
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h32
    obtain ⟨n, hn⟩ := Nat.dvd_of_mod_eq_zero hb
    rw [hn, hm, Nat.mul_assoc, Nat.mul_mod_right]
  have hB1 : (j + 1) * 3329 + 3329 ≤ 32768 := by omega_using [hj]
  have hB2 : (j + 1) * 3329 ≤ 32768 := by omega_using [hj]
  refine bf_ok hxy hx16 hx17 hy16 ht16 hx hy hz ht hq (fun e _ => ?_) hB1 hB2 fun s' c' hx' hy' =>
    k s' c' (?_ : Rep _ _ _) (?_ : Rep _ _ _)
  · simp only [Impl.MlKem.AArch64.Ntt16.zeta]
    by_cases h : K₀ + kz.getD e 0 < 128
    · exact zetaTable_lt _ h
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        rw [zetaTable_eq, zetas_length]; omega_arith)]; decide
  all_goals
    rw [show (j + 1 + 1) * 3329 = (j + 1) * 3329 + 3329 by rw [Nat.succ_mul]]
  · refine hx'.congr fun e he => ?_
    obtain ⟨o1, o2, o3, o4, o5⟩ := hl e he
    obtain ⟨m1, d1⟩ := mod_div_base (o := ox.getD e 0) (Nat.mul_pos (by decide) hlen) hbd
    have hidx : K₀ + kz.getD e 0 < 128 := by
      rw [hK, o5, Nat.add_assoc, ← d1, ← hL]; exact zeta_idx_lt j hj _ (by omega_arith)
    rw [nttL_succ_get P hj (by omega_arith), hL, ite_eq_left (by rw [m1]; exact o3), d1, ← o5,
      ← Nat.add_assoc, ← hK, ← ofNat_zeta hidx, o4, Nat.add_assoc]
  · refine hy'.congr fun e he => ?_
    obtain ⟨o1, o2, o3, o4, o5⟩ := hl e he
    obtain ⟨m1, d1⟩ := mod_div_base (o := ox.getD e 0) (Nat.mul_pos (by decide) hlen) hbd
    obtain ⟨m2, d2⟩ := mod_div_base (o := oy.getD e 0) (Nat.mul_pos (by decide) hlen) hbd
    have hidx : K₀ + kz.getD e 0 < 128 := by
      rw [hK, o5, Nat.add_assoc, ← d1, ← hL]; exact zeta_idx_lt j hj _ (by omega_arith)
    have hm : ¬ oy.getD e 0 % (2 * len) < len := by
      rw [o4]
      have : (ox.getD e 0 + len) % (2 * len) = ox.getD e 0 % (2 * len) + len := by
        rw [Nat.add_mod]
        rw [Nat.mod_eq_of_lt (show len < 2 * len by omega_arith)]
        have := Nat.mod_lt (ox.getD e 0) (show 0 < 2 * len by omega_arith)
        exact Nat.mod_eq_of_lt (by omega_arith)
      omega_arith
    have hq2 : oy.getD e 0 / (2 * len) = ox.getD e 0 / (2 * len) := by
      rw [o4]
      have h1 := Nat.div_add_mod (ox.getD e 0) (2 * len)
      refine Nat.div_eq_of_lt_le ?_ ?_
      · rw [Nat.mul_comm]; omega_arith
      · rw [Nat.succ_mul, Nat.mul_comm]; omega_arith
    rw [nttL_succ_get P hj (by omega_arith), hL, ite_eq_right (by rw [m2]; exact hm), d2, hq2, ← o5,
      ← Nat.add_assoc, ← hK, ← ofNat_zeta hidx, o4,
      show base + (ox.getD e 0 + len) - len = base + ox.getD e 0 by omega_arith]

end

/-! ## Reduction to `[0, q)` -/

theorem vhalf_and (a b : BitVec 128) {e : Nat} : vhalf (a &&& b) e = vhalf a e &&& vhalf b e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_vhalf _ _ hi, BitVec.getLsbD_and]

/-- A lane less than `q` in absolute value made nonnegative: `r + (r >> 15 & q)`. -/
theorem nonneg_lane {r : BitVec 16} (h1 : -3329 < r.toInt) (h2 : r.toInt < 3329) :
    (r + (r.sshiftRight 15 &&& BitVec.ofNat 16 3329)).toInt =
      if r.toInt < 0 then r.toInt + 3329 else r.toInt := by
  rw [BitVec.sshiftRight_eq, Int.shiftRight_eq_div_pow]
  by_cases h : r.toInt < 0
  · rw [show r.toInt / ((2 ^ 15 : Nat) : Int) = -1 by omega_arith, ite_eq_left h,
      show BitVec.ofInt 16 (-1) &&& BitVec.ofNat 16 3329 = BitVec.ofNat 16 3329 by decide,
      BitVec.toInt_add]
    simp only [Int.bmod_def, show (BitVec.ofNat 16 3329).toInt = 3329 by decide]
    split <;> omega_arith
  · rw [show r.toInt / ((2 ^ 15 : Nat) : Int) = 0 by omega_arith, ite_eq_right h,
      show BitVec.ofInt 16 0 &&& BitVec.ofNat 16 3329 = 0#16 by decide, BitVec.add_zero]

theorem tw_one : tw 1 = 10 := by decide

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `normalize x`: the lanes of `x`, less than `2¹⁵` in absolute value, reduced to `[0, q)`. -/
theorem norm_ok {x : VReg} (h16 : x ≠ .v16 := by decide) (h31 : x ≠ .v31 := by decide) {X : Nat → Zq} {B : Nat}
    (hx : Rep (s.v x) X B) (hB : B ≤ 32768) (h10 : Cst (s.v .v30) fun _ => 10)
    (hq : Cst (s.v .v31) fun _ => 3329)
    (k : ∀ s', VChg [.v16, x, .v16, .v16, x] s s' → (∀ e < 8, (vhalf (s'.v x) e).toNat = (X e).val) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (normalize x ++ rest)) s Q := by
  simp only [normalize, List.cons_append, List.nil_append]
  have L : ∀ e < 8, ∃ T, sqdmulhHLane true (vhalf (s.v x) e) (BitVec.ofNat 16 10) = some T ∧
      -3329 < (vhalf (s.v x) e - T * BitVec.ofNat 16 3329).toInt ∧
      (vhalf (s.v x) e - T * BitVec.ofNat 16 3329).toInt < 3329 ∧
      ((vhalf (s.v x) e - T * BitVec.ofNat 16 3329).toInt - ((X e).val : Int)) % 3329 = 0 := by
    intro e he
    obtain ⟨a1, a2, a3⟩ := hx e he
    obtain ⟨T, hT, b1, b2, b3⟩ := mm_ok (vhalf (s.v x) e) (z := 1) (by omega_arith) (by decide)
    rw [tw_one, show (vhalf (s.v x) e) * BitVec.ofNat 16 1 = vhalf (s.v x) e from BitVec.mul_one _]
      at *
    refine ⟨T, hT, b1, b2, ?_⟩
    omega_arith
  refine wp_vop (eval_mulH fun e he => by
    obtain ⟨T, hT, -⟩ := L e he
    simp only [VMulHOp.lane, h10 e he, hT, Option.isSome_some]) fun s₁ h₁ => ?_
  refine wp_vop (eval_mulH fun _ _ => rfl) fun s₂ h₂ => ?_
  refine wp_vop rfl fun s₃ h₃ => wp_vop rfl fun s₄ h₄ => wp_vop rfl fun s₅ h₅ => ?_
  refine k s₅ ((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans h₅.chg) fun e he => ?_
  obtain ⟨T, hT, c1, c2, c3⟩ := L e he
  have r2 : vhalf (s₂.v x) e = vhalf (s.v x) e - T * BitVec.ofNat 16 3329 := by
    rw [h₂.v, vhalf_ofVHalves _ he]
    simp only [VMulHOp.lane, h₁.v, h₁.get x h16, h₁.get .v31, vhalf_ofVHalves _ he, h10 e he, hT,
      Option.getD_some, hq e he]
  generalize vhalf (s.v x) e - T * BitVec.ofNat 16 3329 = r at r2 c1 c2 c3
  have r5 : vhalf (s₅.v x) e = r + (r.sshiftRight 15 &&& BitVec.ofNat 16 3329) := by
    rw [h₅.v, vhalf_map2 _ _ _ he, h₄.get x h16, h₄.v, vhalf_and, h₃.get x h16,
      h₃.v, vhalf_map2 _ _ _ he, h₃.get .v31, h₂.get .v31 (Ne.symm h31), h₁.get .v31, hq e he, r2]
    rfl
  have hv := val_lt (X e)
  have nn := nonneg_lane c1 c2
  rw [r5]
  rw [BitVec.toInt_eq_toNat_cond] at nn
  split at nn <;> split at nn <;> omega_arith

end

end VG.Proof.MlKem.AArch64.Ntt16
