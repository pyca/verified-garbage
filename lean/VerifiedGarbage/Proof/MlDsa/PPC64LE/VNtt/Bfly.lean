module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Lanes
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.VNtt
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Block

/-! # ML-DSA's vector NTT on PPC64LE: the butterfly

`bfly` run one instruction at a time (`wp_vop`), each result named by the
lane operation it is (`subV`, `minV`, …), then the lanes of its two results
from `bfly_lane` (`bfly_run`). -/

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

end VG.Proof.MlDsa.PPC64LE.VNtt
