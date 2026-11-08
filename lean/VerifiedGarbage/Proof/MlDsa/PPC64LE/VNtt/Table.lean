module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Lanes
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Mem
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.VNtt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # ML-DSA's vector NTT on PPC64LE: the butterfly and the zetas

`bfly` run one instruction at a time (`wp_vop`), each result named by the
lane operation it is (`subV`, `minV`, …), then the lanes of its two results
from `bfly_lane` (`bfly_lanes`).

`z'` of each zeta, stored in `scratch` at the positions `scrK` says
(`scrK_wide`, `scrK_two`, …), and `z` from it (`zrec`): no zeta is 0
modulo `q` (`zeta_nz`). -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.VNtt

/-! ## Lane operations -/

def addV (x y : BitVec 128) : BitVec 128 := ofVWords fun i => vword x i + vword y i
def subV (x y : BitVec 128) : BitVec 128 := ofVWords fun i => vword x i - vword y i
def minV (x y : BitVec 128) : BitVec 128 := ofVWords fun i => minu32 (vword x i) (vword y i)
def loV (x y : BitVec 128) : BitVec 128 := ofVWords fun i => vword x i * vword y i
def mulEV (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 64 ((vword x 0).toNat * (vword y 0).toNat) ++ BitVec.ofNat 64 ((vword x 2).toNat * (vword y 2).toNat)
def mulOV (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 64 ((vword x 1).toNat * (vword y 1).toNat) ++ BitVec.ofNat 64 ((vword x 3).toNat * (vword y 3).toNat)

theorem eval_add (v : VReg → BitVec 128) (d n m : VReg) :
    VOp.eval v (.add false d n m) = some (d, addV (v n) (v m)) := rfl
theorem eval_sub (v : VReg → BitVec 128) (d n m : VReg) :
    VOp.eval v (.sub true d n m) = some (d, subV (v n) (v m)) := rfl
theorem eval_min (v : VReg → BitVec 128) (d n m : VReg) :
    VOp.eval v (.minu true d n m) = some (d, minV (v n) (v m)) := rfl
theorem eval_lo (v : VReg → BitVec 128) (d n m : VReg) :
    VOp.eval v (.muluwm d n m) = some (d, loV (v n) (v m)) := rfl
theorem eval_mulE (v : VReg → BitVec 128) (d n m : VReg) :
    VOp.eval v (.mulu false true d n m) = some (d, mulEV (v n) (v m)) := rfl
theorem eval_mulO (v : VReg → BitVec 128) (d n m : VReg) :
    VOp.eval v (.mulu true true d n m) = some (d, mulOV (v n) (v m)) := rfl
theorem eval_perm (v : VReg → BitVec 128) (d n m c : VReg) :
    VOp.eval v (.perm d n m c) = some (d, permV (v n) (v m) (v c)) := rfl

theorem syms_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).syms = s.syms := rfl

theorem wp_vop {op : VOp} {d : VReg} {x : BitVec 128} {is : List Instr} {s : State} {Q : State → Prop}
    (h : VOp.eval s.vpr op = some (d, x)) (k : WP isa (.block is) (s.writeV d x) Q) :
    WP isa (.block (.vop op :: is)) s Q :=
  WP.block_cons_iff.2 ⟨_, show (VOp.eval s.vpr op).map _ = _ by rw [h]; rfl, k⟩

/-! ## The butterfly's results -/

/-- `t = z·b mod q`, as `bfly` computes it in `v7`. -/
def bflyT (b z zp qv c : BitVec 128) : BitVec 128 :=
  minV (subV (loV b z) (loV (permV (mulEV b zp) (mulOV b zp) c) qv))
    (subV (subV (loV b z) (loV (permV (mulEV b zp) (mulOV b zp) c) qv)) qv)

def bflyA (a b z zp qv c : BitVec 128) : BitVec 128 :=
  minV (addV a (bflyT b z zp qv c)) (subV (addV a (bflyT b z zp qv c)) qv)

def bflyB (a b z zp qv c : BitVec 128) : BitVec 128 :=
  minV (subV a (bflyT b z zp qv c)) (addV (subV a (bflyT b z zp qv c)) qv)

/-- The pairs of registers `bfly` runs on. -/
def Pair (a b : VReg) : Prop :=
  (a = .v0 ∧ b = .v1) ∨ (a = .v9 ∧ b = .v11) ∨ (a = .v8 ∧ b = .v10) ∨ (a = .v9 ∧ b = .v8) ∨
    (a = .v11 ∧ b = .v10)

set_option linter.unusedSimpArgs false in
theorem bfly_exec (s : State) {a b : VReg} (hp : Pair a b) :
    WP isa (.block (bfly a b .v2 .v3)) s fun t =>
      t.vpr a = bflyA (s.vpr a) (s.vpr b) (s.vpr .v2) (s.vpr .v3) (s.vpr .v4) (s.vpr .v5) ∧
      t.vpr b = bflyB (s.vpr a) (s.vpr b) (s.vpr .v2) (s.vpr .v3) (s.vpr .v4) (s.vpr .v5) ∧
      VOnly [a, b, .v6, .v7] s t ∧ t.syms = s.syms := by
  unfold bfly
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · refine wp_vop (eval_mulE _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_mulO _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_lo _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_lo _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_min _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_add _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_sub _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_min _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_add _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine wp_vop (eval_min _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
    refine WP.block_nil ?_
    refine ⟨rfl, rfl, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    rotate_left
    all_goals try simp only [gpr_writeV, mem_writeV, rd_writeV, wr_writeV, sp_writeV, lr_writeV, syms_writeV]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3, r4⟩ := hr
    simp only [vpr_writeV, r1, r2, r3, r4, ite_false]

/-! ## The butterfly's lanes -/

theorem vword_addV (x y : BitVec 128) {i : Nat} (hi : i < 4) : vword (addV x y) i = vword x i + vword y i :=
  vword_ofVWords _ hi
theorem vword_subV (x y : BitVec 128) {i : Nat} (hi : i < 4) : vword (subV x y) i = vword x i - vword y i :=
  vword_ofVWords _ hi
theorem vword_minV (x y : BitVec 128) {i : Nat} (hi : i < 4) :
    vword (minV x y) i = minu32 (vword x i) (vword y i) := vword_ofVWords _ hi
theorem vword_loV (x y : BitVec 128) {i : Nat} (hi : i < 4) : vword (loV x y) i = vword x i * vword y i :=
  vword_ofVWords _ hi

/-- The control of the high words of the even and odd products: lanes 0, 4,
2, 6 of `VA || VB`. -/
def hiC : BitVec 128 := 0x000102031011121308090a0b18191a1b#128

theorem prod_lt (x y : BitVec 32) : x.toNat * y.toNat < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' x.isLt y.isLt) (by decide)

theorem vword_hi (b zp : BitVec 128) {i : Nat} (hi : i < 4) :
    (vword (permV (mulEV b zp) (mulOV b zp) hiC) i).toNat = (vword b i).toNat * (vword zp i).toNat / 2 ^ 32 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [vword_permV _ _ _ (k := 0) (by decide) (by decide) (by decide), ite_eq_left (by decide), mulEV,
      (vword_dw_hi _ _).1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (prod_lt _ _)]
  · rw [vword_permV _ _ _ (k := 4) (by decide) (by decide) (by decide), ite_eq_right (by decide), mulOV,
      show 4 - 4 = 0 from rfl, (vword_dw_hi _ _).1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (prod_lt _ _)]
  · rw [vword_permV _ _ _ (k := 2) (by decide) (by decide) (by decide), ite_eq_left (by decide), mulEV,
      (vword_dw_hi _ _).2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (prod_lt _ _)]
  · rw [vword_permV _ _ _ (k := 6) (by decide) (by decide) (by decide), ite_eq_right (by decide), mulOV,
      show 6 - 4 = 2 from rfl, (vword_dw_hi _ _).2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (prod_lt _ _)]

open VG.Spec.MlDsa (Zq)

/-- Lane `i` of the butterfly's results, from its operands' lanes. -/
theorem bfly_lanes {A B Z ZP Q : BitVec 128} {x y z : Zq} {i : Nat} (hi : i < 4)
    (hA : (vword A i).toNat = x.val) (hB : (vword B i).toNat = y.val) (hZ : (vword Z i).toNat = z.val)
    (hZP : (vword ZP i).toNat = z.val * 2 ^ 32 / Spec.MlDsa.q) (hQ : (vword Q i).toNat = Spec.MlDsa.q) :
    (vword (bflyA A B Z ZP Q hiC) i).toNat = (x + z * y).val ∧
    (vword (bflyB A B Z ZP Q hiC) i).toNat = (x - z * y).val := by
  simp only [bflyA, bflyB, bflyT, vword_minV _ _ hi, vword_addV _ _ hi, vword_subV _ _ hi, vword_loV _ _ hi]
  exact bfly_lane (vword A i) (vword B i) _ (vword Q i) (vword Z i) (vword ZP i) x y z hQ hZ hZP hA hB
    (vword_hi B ZP hi)

/-! ## Zetas -/

theorem zeta_lt (m : Nat) : zeta m < Spec.MlDsa.q := Nat.mod_lt _ (by decide)

theorem shoup_lt {z : Nat} (hz : z < Spec.MlDsa.q) : shoup z < 2 ^ 32 := by
  unfold shoup q
  have : z * 2 ^ 32 < 8380417 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hz (by decide)
  omega

/-- Multiplying by `c` with an inverse `d` modulo `q` keeps a residue nonzero. -/
theorem mul_mod_ne {c d x : Nat} (hcd : c * d % 8380417 = 1) (hx : x % 8380417 ≠ 0) : c * x % 8380417 ≠ 0 := by
  intro h
  apply hx
  have : x * (c * d) % 8380417 = x % 8380417 := by rw [Nat.mul_mod, hcd, Nat.mul_one, Nat.mod_mod]
  rw [← this, show x * (c * d) = c * x * d by rw [Nat.mul_comm c x, Nat.mul_assoc], Nat.mul_mod, h, Nat.zero_mul,
    Nat.zero_mod]

theorem pow_ne (b : Nat) : 1753 ^ b % 8380417 ≠ 0 := by
  induction b with
  | zero => decide
  | succ b ih => rw [Nat.pow_succ, Nat.mul_comm]; exact mul_mod_ne (d := 731434) (by decide) ih

/-- No zeta times `2³²` is 0 modulo `q`. -/
theorem zeta_nz (k : Nat) : zeta k * 2 ^ 32 % 8380417 ≠ 0 := by
  rw [Nat.mul_comm]
  refine mul_mod_ne (d := 8265825) (by decide) ?_
  rw [zeta, q, Nat.mod_mod]; exact pow_ne _

/-- `z` from `z'`: `⌊z' · q / 2³²⌋ + 1`. -/
theorem zrec {z : Nat} (hnz : z * 2 ^ 32 % 8380417 ≠ 0) : shoup z * 8380417 / 2 ^ 32 + 1 = z := by
  unfold shoup q
  omega

/-! ## Positions -/

theorem flip_eq {e : Nat} (he : e < 4) : swap1 e = e ^^^ 1 := by
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem flip_lt {e : Nat} (he : e < 4) : swap1 e < 4 := by unfold swap1; split <;> omega

theorem scrK_wide {k : Nat} (h : k < 64) : scrK k = k := by
  unfold scrK; rw [ite_eq_left h]

theorem scrK_two {g r : Nat} (hg : g < 16) (hr : r < 4) : scrK (64 + 4 * g + swap1 r) = 64 + 4 * g + r := by
  unfold scrK swap1
  rw [ite_eq_right (by split <;> omega), ite_eq_left (by split <;> omega)]
  split <;> split <;> omega

theorem scrK_even {g r : Nat} (hg : g < 16) (hr : r < 4) :
    scrK (128 + 8 * g + swap1 r) = 128 + 8 * g + 2 * r := by
  unfold scrK swap1
  rw [ite_eq_right (by split <;> omega), ite_eq_right (by split <;> omega), ite_eq_left (by split <;> omega)]
  split <;> split <;> omega

theorem scrK_odd {g r : Nat} (hg : g < 16) (hr : r < 4) :
    scrK (132 + 8 * g + swap1 r) = 128 + 8 * g + 2 * r + 1 := by
  unfold scrK swap1
  rw [ite_eq_right (by split <;> omega), ite_eq_right (by split <;> omega), ite_eq_right (by split <;> omega)]
  split <;> split <;> omega

theorem scrK_lt {p : Nat} (hp : p < 256) : scrK p < 256 := by
  unfold scrK swap1; repeat' split
  all_goals omega

/-! ## Storing the table -/

theorem loadImm_lo_bits (a b : BitVec 16) :
    ((a ++ (0 : BitVec 16)).signExtend 64 ||| b.setWidth 64).setWidth 32 = a ++ b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_signExtend, BitVec.getLsbD_append, hi,
    decide_true, Bool.true_and, show i < 64 by omega]
  by_cases h : i < 16
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge b i (by omega)]

theorem loadImm_lo {v : Nat} (hv : v < 2 ^ 32) :
    ((BitVec.ofNat 16 (v / 65536) ++ (0 : BitVec 16)).signExtend 64 |||
      (BitVec.ofNat 16 (v % 65536)).setWidth 64).setWidth 32 = BitVec.ofNat 32 v := by
  rw [loadImm_lo_bits]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.shiftLeft_eq]
  omega

theorem scrV_lt (p : Nat) : scrV p < 2 ^ 32 := shoup_lt (zeta_lt _)

/-- After positions `1 … k` of the table at `r4`. -/
structure FillInv (K : Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  vpr : s.vpr = s₀.vpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  syms : s.syms = s₀.syms
  frame : Frame [⟨s₀.gpr .r4, 1024⟩] s₀.mem s.mem
  tab : ∀ p, 0 < p → p ≤ k → s.mem.readW (s₀.gpr .r4 + BitVec.ofNat 64 (4 * p)) 32 = BitVec.ofNat 32 (shoup (zeta (K p)))

theorem fill_ok (K : Nat → Nat) {s₀ : State} (hwr : ∀ p < 256, InRegions s₀.wr (s₀.gpr .r4 + BitVec.ofNat 64 (4 * p)) 4) :
    WP isa (.block (fillK K)) s₀ (FillInv K s₀ 255) := by
  refine wp_range_flatMap (M := isa) (FillInv K s₀) (fun k s hk h => ?_) 255 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun p hp hp' => absurd hp' (by omega)⟩
  have hv := shoup_lt (zeta_lt (K (k + 1)))
  let s₁ := s.write .r12 ((BitVec.ofNat 16 (shoup (zeta (K (k + 1))) / 65536) ++ (0 : BitVec 16)).signExtend 64)
  let s₂ := s₁.write .r12 (s₁.gpr .r12 ||| (BitVec.ofNat 16 (shoup (zeta (K (k + 1))) % 65536)).setWidth 64)
  have v2 : (s₂.gpr .r12).setWidth 32 = BitVec.ofNat 32 (shoup (zeta (K (k + 1)))) := by
    simp only [s₂, s₁, State.write, ite_true]; exact loadImm_lo hv
  have e : s₂.gpr .r4 + BitVec.ofNat 64 (4 * (k + 1)) = s₀.gpr .r4 + BitVec.ofNat 64 (4 * (k + 1)) := by
    simp only [s₂, s₁, State.write, reduceCtorEq, ite_false, h.gpr .r4 (by decide)]
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_store_w (by decide) (show 4 * (k + 1) < 2 ^ 15 by omega)
    (by show InRegions s₂.wr _ 4; rw [e]; exact h.wr ▸ hwr (k + 1) (by omega))) (wp_nil ?_)))
  show FillInv K s₀ (k + 1)
    { s₂ with mem := (s₂.mem.writeW (s₂.gpr .r4 + BitVec.ofNat 64 (4 * (k + 1))) ((s₂.gpr .r12).setWidth 32)) }
  rw [e, v2]
  refine ⟨fun r hr => ?_, h.vpr, h.rd, h.wr, h.sp, h.lr, h.syms, ?_, fun p hp hp' => ?_⟩
  · simp only [s₂, s₁, State.write, hr, ite_false]; exact h.gpr r hr
  · exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · show (s.mem.writeW _ _).readW _ 32 = _
    by_cases ep : p = k + 1
    · subst ep; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.tab p hp (by omega)

/-! ## The constants -/

theorem hi64_append (a b : BitVec 64) : (a ++ b).extractLsb' 64 64 = a := BitVec.extractLsb'_append_eq_left
theorem lo64_append (a b : BitVec 64) : (a ++ b).extractLsb' 0 64 = b := BitVec.extractLsb'_append_eq_right

set_option linter.unusedSimpArgs false in
theorem vconst_run (u : State) {d : VReg} (h6 : d ≠ .v6) (h7 : d ≠ .v7) (hi lo : Nat) :
    WP isa (.block (vconst d hi lo)) u fun t =>
      t.vpr d = BitVec.ofNat 64 hi ++ BitVec.ofNat 64 lo ∧ (∀ r, r ≠ d → r ≠ .v6 → r ≠ .v7 → t.vpr r = u.vpr r) ∧
      (∀ r, r ≠ .r11 → r ≠ .r12 → t.gpr r = u.gpr r) ∧ t.mem = u.mem ∧ t.rd = u.rd ∧ t.wr = u.wr ∧
      t.sp = u.sp ∧ t.lr = u.lr ∧ t.syms = u.syms := by
  unfold vconst
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (const64_ok .r12 _ u) fun u₁ e₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok .r11 _ u₁) fun u₂ e₂ => ?_
  subst e₁ e₂
  refine WP.cons rfl (WP.cons rfl (WP.cons (exec_sldoi8 _ _ _ _) (WP.cons (exec_sldoi8 _ _ _ _) (wp_nil ?_))))
  simp only [vpr_writeV, h6, h7, ite_true, ite_false, reduceCtorEq, Ne.symm h6, Ne.symm h7]
  refine ⟨?_, fun r h1 h2 h3 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [State.writeV, State.write, ite_true, reduceCtorEq, ite_false, lo64_append, hi64_append]
  · simp only [State.writeV, State.write, h1, h2, h3, ite_false]
  · simp only [State.writeV, State.write, h1, h2, ite_false]

def caC : BitVec 128 := 0x00010203101112130405060714151617#128
def cbC : BitVec 128 := 0x08090a0b18191a1b0c0d0e0f1c1d1e1f#128
def ccC : BitVec 128 := 0x00010203040506071011121314151617#128
def cdC : BitVec 128 := 0x08090a0b0c0d0e0f18191a1b1c1d1e1f#128

theorem vword_append (x y : BitVec 64) :
    vword (x ++ y) 0 = x.extractLsb' 32 32 ∧ vword (x ++ y) 1 = x.extractLsb' 0 32 ∧
    vword (x ++ y) 2 = y.extractLsb' 32 32 ∧ vword (x ++ y) 3 = y.extractLsb' 0 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro r hr
    simp only [vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hr, decide_true, Bool.true_and]
    split <;> first | omega | exact congrArg _ (by omega)

/-- The state the constants leave. -/
structure ConstsOut (u t : State) : Prop where
  q : ∀ i < 4, (vword (t.vpr .v4) i).toNat = Spec.MlDsa.q
  v5 : t.vpr .v5 = hiC
  v16 : t.vpr .v16 = caC
  v17 : t.vpr .v17 = cbC
  v18 : t.vpr .v18 = ccC
  v19 : t.vpr .v19 = cdC
  vpr : ∀ r, r ∉ [.v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19] → t.vpr r = u.vpr r
  gpr : ∀ r, r ≠ .r11 → r ≠ .r12 → t.gpr r = u.gpr r
  mem : t.mem = u.mem
  rd : t.rd = u.rd
  wr : t.wr = u.wr
  sp : t.sp = u.sp
  lr : t.lr = u.lr
  syms : t.syms = u.syms

set_option linter.unusedSimpArgs false in
theorem consts_run (u : State) : WP isa (.block consts) u (ConstsOut u) := by
  unfold consts ctl
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.cons exec_lis (WP.cons exec_ori (wp_nil ?_))
  rw [WP.block_append_iff]
  refine WP.cons rfl (WP.cons rfl (wp_nil ?_))
  rw [WP.block_append_iff]
  refine WP.mono (vconst_run _ (d := .v5) (by decide) (by decide) _ _) fun t₅ ⟨d₅, v₅, g₅, m₅, rd₅, wr₅, sp₅, lr₅, sy₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vconst_run _ (d := .v16) (by decide) (by decide) _ _)
    fun t₁₆ ⟨d₁₆, v₁₆, g₁₆, m₁₆, rd₁₆, wr₁₆, sp₁₆, lr₁₆, sy₁₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vconst_run _ (d := .v17) (by decide) (by decide) _ _)
    fun t₁₇ ⟨d₁₇, v₁₇, g₁₇, m₁₇, rd₁₇, wr₁₇, sp₁₇, lr₁₇, sy₁₇⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vconst_run _ (d := .v18) (by decide) (by decide) _ _)
    fun t₁₈ ⟨d₁₈, v₁₈, g₁₈, m₁₈, rd₁₈, wr₁₈, sp₁₈, lr₁₈, sy₁₈⟩ => ?_
  refine WP.mono (vconst_run _ (d := .v19) (by decide) (by decide) _ _)
    fun t ⟨d₁₉, v₁₉, g₁₉, m₁₉, rd₁₉, wr₁₉, sp₁₉, lr₁₉, sy₁₉⟩ => ?_
  have q4 : ∀ i < 4, (vword (t.vpr .v4) i).toNat = Spec.MlDsa.q := fun i hi => by
    rw [v₁₉ _ (by decide) (by decide) (by decide), v₁₈ _ (by decide) (by decide) (by decide),
      v₁₇ _ (by decide) (by decide) (by decide), v₁₆ _ (by decide) (by decide) (by decide),
      v₅ _ (by decide) (by decide) (by decide)]
    simp only [State.writeV, State.write, ite_true]
    have e32 : ∀ x : BitVec 64, x.extractLsb' 0 32 = x.setWidth 32 := fun x => by
      apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]
    rw [vword_ofVWords _ hi, (vword_append _ _).2.1, e32, loadImm_lo (by decide)]
    rfl
  have nv : ∀ r, r ∉ [.v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19] → t.vpr r = u.vpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h4, h5, h6, h7, h16, h17, h18, h19⟩ := hr
    rw [v₁₉ _ h19 h6 h7, v₁₈ _ h18 h6 h7, v₁₇ _ h17 h6 h7, v₁₆ _ h16 h6 h7, v₅ _ h5 h6 h7]
    simp only [State.writeV, State.write, h4, ite_false]
  refine ⟨q4, ?_, ?_, ?_, ?_, ?_, nv, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₁₉ _ (by decide) (by decide) (by decide), v₁₈ _ (by decide) (by decide) (by decide),
      v₁₇ _ (by decide) (by decide) (by decide), v₁₆ _ (by decide) (by decide) (by decide), d₅]; decide
  · rw [v₁₉ _ (by decide) (by decide) (by decide), v₁₈ _ (by decide) (by decide) (by decide),
      v₁₇ _ (by decide) (by decide) (by decide), d₁₆]; decide
  · rw [v₁₉ _ (by decide) (by decide) (by decide), v₁₈ _ (by decide) (by decide) (by decide), d₁₇]; decide
  · rw [v₁₉ _ (by decide) (by decide) (by decide), d₁₈]; decide
  · rw [d₁₉]; decide
  · rw [g₁₉ r h1 h2, g₁₈ r h1 h2, g₁₇ r h1 h2, g₁₆ r h1 h2, g₅ r h1 h2]
    simp only [State.writeV, State.write, h1, h2, ite_false]
  · rw [m₁₉, m₁₈, m₁₇, m₁₆, m₅]; rfl
  · rw [rd₁₉, rd₁₈, rd₁₇, rd₁₆, rd₅]; rfl
  · rw [wr₁₉, wr₁₈, wr₁₇, wr₁₆, wr₅]; rfl
  · rw [sp₁₉, sp₁₈, sp₁₇, sp₁₆, sp₅]; rfl
  · rw [lr₁₉, lr₁₈, lr₁₇, lr₁₆, lr₅]; rfl
  · rw [sy₁₉, sy₁₈, sy₁₇, sy₁₆, sy₅]; rfl

/-! ## `z` from `z'` -/

theorem eval_one (v : VReg → BitVec 128) (d : VReg) :
    VOp.eval v (.splatImm true d 1) = some (d, ofVWords fun _ => BitVec.ofInt 32 1) := rfl

set_option linter.unusedSimpArgs false in
theorem zcalc_run (u : State) (hq : ∀ i < 4, (vword (u.vpr .v4) i).toNat = Spec.MlDsa.q) (h5 : u.vpr .v5 = hiC)
    {z : Nat → Nat} (hzq : ∀ i < 4, z i < Spec.MlDsa.q) (hz : ∀ i < 4, z i * 2 ^ 32 % 8380417 ≠ 0)
    (h3 : ∀ i < 4, (vword (u.vpr .v3) i).toNat = shoup (z i)) :
    WP isa (.block zcalc) u fun t => (∀ i < 4, (vword (t.vpr .v2) i).toNat = z i) ∧
      VOnly [.v2, .v6, .v7] u t ∧ t.syms = u.syms := by
  unfold zcalc
  refine wp_vop (eval_mulE _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_mulO _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_perm _ _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_one _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine wp_vop (eval_add _ _ _ _) ?_; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  refine WP.block_nil ⟨fun i hi => ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp only [vpr_writeV, ite_true]
    rw [h5, vword_addV _ _ hi, vword_ofVWords _ hi, BitVec.toNat_add, vword_hi _ _ hi, h3 i hi, hq i hi]
    have h1 := shoup_lt (hzq i hi)
    have hs : shoup (z i) * Spec.MlDsa.q / 2 ^ 32 < 2 ^ 32 - 1 := by
      generalize shoup (z i) = x at h1 ⊢
      show x * 8380417 / 2 ^ 32 < 2 ^ 32 - 1
      omega
    rw [show (BitVec.ofInt 32 1).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
    exact zrec (hz i hi)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.MlDsa.PPC64LE.VNtt
