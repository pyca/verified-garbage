module

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Stage
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Arith

/-!
# P-256 on x86-64 with AVX512_IFMA: sums, differences and choices of field vectors

What the terms of the operations between the products (`fadd`, `fsub`,
`fshl`, `fperm`, `fblend`, the masked sums and differences, `fbias`) are as
numbers (`vI`), lane by lane.
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

/-!
## The field's operations, as integers

What the terms of `norm`, `mulCore` and `sqrCore` (read with `tops`) are as
integers (`T.int`), for any terms they are given.
-/

section

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma

theorem pick4_same {α : Type} (a : α) (k : Nat) : pick4 a a a a k = a := by
  unfold pick4; split <;> rfl

theorem maskOf_mask : maskOf (klit kMask) = some (52, 52, 52, 52) := by decide
theorem maskOf_m48 : maskOf (klit kM48) = some (48, 48, 48, 48) := by decide

theorem andc_mask (a : T) : tops.andc a kMask = .mask a 52 52 52 52 := by
  simp only [tops, maskOf_mask]
theorem andc_m48 (a : T) : tops.andc a kM48 = .mask a 48 48 48 48 := by
  simp only [tops, maskOf_m48]

theorem mask52_int (a : T) (E : Env) (k : Nat) : (T.mask a 52 52 52 52).int E k = a.int E k % 2 ^ 52 := by
  simp only [T.int, pick4_same, Nat.reduceLeDiff, ↓reduceIte]
theorem mask48_int (a : T) (E : Env) (k : Nat) : (T.mask a 48 48 48 48).int E k = a.int E k % 2 ^ 48 := by
  simp only [T.int, pick4_same, Nat.reduceLeDiff, ↓reduceIte]

/-- The limbs of a field vector's lane `k`, as integers. -/
def li (E : Env) (k : Nat) (v : F5 T) : Int × Int × Int × Int × Int :=
  (v.l0.int E k, v.l1.int E k, v.l2.int E k, v.l3.int E k, v.l4.int E k)

/-- The number lane `k` of a field vector stands for. -/
def vI (E : Env) (k : Nat) (v : F5 T) : Int :=
  val5 (v.l0.int E k) (v.l1.int E k) (v.l2.int E k) (v.l3.int E k) (v.l4.int E k)

/-- `norm`, as integers. -/
theorem norm_int (v : F5 T) (E : Env) (k : Nat) :
    li E k (Id.run (norm tops v)) =
      normI (v.l0.int E k) (v.l1.int E k) (v.l2.int E k) (v.l3.int E k) (v.l4.int E k) := by
  simp only [norm, Id.run, bind, pure, andc_mask, andc_m48, li, normI]
  simp only [tops, T.int, pick4_same, Nat.reduceLeDiff, ↓reduceIte]

/-- The reduction, as integers; its first column is not a shift left (which `shrOf` would take
with the shift right of it). -/
theorem reduce_int (d t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : T) (h0 : shrOf t0 52 = .shr t0 52) (E : Env) (k : Nat) :
    li E k (Id.run (reduce tops d [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9])) =
      reduceI [t0.int E k, t1.int E k, t2.int E k, t3.int E k, t4.int E k, t5.int E k, t6.int E k, t7.int E k, t8.int E k, t9.int E k] := by
  simp only [reduce, redStep, Id.run, bind, pure, andc_mask, List.getD_cons_zero, List.getD_cons_succ,
    List.set_cons_zero, List.set_cons_succ, li, reduceI, redI]
  simp only [tops, Option.getD_some]
  simp only [h0]
  have c1 : ((2 ^ 36 : Nat) : Int) = 2 ^ 36 := by decide
  have c2 : ((2 ^ 48 - 2 ^ 16 : Nat) : Int) = 2 ^ 48 - 2 ^ 16 := by decide
  simp only [shrOf, T.int, klit, k36, kP4, K4.all, pick4_same, lo52, hi52, Nat.reduceLeDiff, ↓reduceIte, c1, c2]

/-- The columns of a product. -/
def mulColsT (a b : F5 T) : List T :=
  [.mad false (.lit 0 0 0 0) a.l0 b.l0,
    .add (.mad false (.mad false (.lit 0 0 0 0) a.l0 b.l1) a.l1 b.l0) (.mad true (.lit 0 0 0 0) a.l0 b.l0),
    .add (.mad false (.mad false (.mad false (.lit 0 0 0 0) a.l0 b.l2) a.l1 b.l1) a.l2 b.l0) (.mad true (.mad true (.lit 0 0 0 0) a.l0 b.l1) a.l1 b.l0),
    .add (.mad false (.mad false (.mad false (.mad false (.lit 0 0 0 0) a.l0 b.l3) a.l1 b.l2) a.l2 b.l1) a.l3 b.l0) (.mad true (.mad true (.mad true (.lit 0 0 0 0) a.l0 b.l2) a.l1 b.l1) a.l2 b.l0),
    .add (.mad false (.mad false (.mad false (.mad false (.mad false (.lit 0 0 0 0) a.l0 b.l4) a.l1 b.l3) a.l2 b.l2) a.l3 b.l1) a.l4 b.l0) (.mad true (.mad true (.mad true (.mad true (.lit 0 0 0 0) a.l0 b.l3) a.l1 b.l2) a.l2 b.l1) a.l3 b.l0),
    .add (.mad false (.mad false (.mad false (.mad false (.lit 0 0 0 0) a.l1 b.l4) a.l2 b.l3) a.l3 b.l2) a.l4 b.l1) (.mad true (.mad true (.mad true (.mad true (.mad true (.lit 0 0 0 0) a.l0 b.l4) a.l1 b.l3) a.l2 b.l2) a.l3 b.l1) a.l4 b.l0),
    .add (.mad false (.mad false (.mad false (.lit 0 0 0 0) a.l2 b.l4) a.l3 b.l3) a.l4 b.l2) (.mad true (.mad true (.mad true (.mad true (.lit 0 0 0 0) a.l1 b.l4) a.l2 b.l3) a.l3 b.l2) a.l4 b.l1),
    .add (.mad false (.mad false (.lit 0 0 0 0) a.l3 b.l4) a.l4 b.l3) (.mad true (.mad true (.mad true (.lit 0 0 0 0) a.l2 b.l4) a.l3 b.l3) a.l4 b.l2),
    .add (.mad false (.lit 0 0 0 0) a.l4 b.l4) (.mad true (.mad true (.lit 0 0 0 0) a.l3 b.l4) a.l4 b.l3),
    .mad true (.lit 0 0 0 0) a.l4 b.l4]

theorem range5 : List.range 5 = [0, 1, 2, 3, 4] := by decide
theorem range10 : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide

theorem mulCols_eq (a b : F5 T) : Id.run (mulCols tops a b) = mulColsT a b := by
  have rep : List.replicate 10 (none : Option T) = [none, none, none, none, none, none, none, none, none, none] := rfl
  simp only [mulCols, range5, range10, rep, Id.run, bind, pure, List.foldlM_cons, List.foldlM_nil, List.mapM_cons,
    List.mapM_nil, List.getD_cons_zero, List.getD_cons_succ, List.set_cons_zero, List.set_cons_succ, Nat.reduceAdd,
    F5.get, tops, Option.getD_some, Option.getD_none, mulColsT]

/-- The columns of a square. -/
def sqrColsT (a : F5 T) : List T :=
  [.mad false (.lit 0 0 0 0) a.l0 a.l0,
    .mad true (.add (.mad false (.lit 0 0 0 0) a.l0 a.l1) (.mad false (.lit 0 0 0 0) a.l0 a.l1)) a.l0 a.l0,
    .mad false (.add (.mad true (.mad false (.lit 0 0 0 0) a.l0 a.l2) a.l0 a.l1) (.mad true (.mad false (.lit 0 0 0 0) a.l0 a.l2) a.l0 a.l1)) a.l1 a.l1,
    .mad true (.add (.mad true (.mad false (.mad false (.lit 0 0 0 0) a.l0 a.l3) a.l1 a.l2) a.l0 a.l2) (.mad true (.mad false (.mad false (.lit 0 0 0 0) a.l0 a.l3) a.l1 a.l2) a.l0 a.l2)) a.l1 a.l1,
    .mad false (.add (.mad true (.mad true (.mad false (.mad false (.lit 0 0 0 0) a.l0 a.l4) a.l1 a.l3) a.l0 a.l3) a.l1 a.l2) (.mad true (.mad true (.mad false (.mad false (.lit 0 0 0 0) a.l0 a.l4) a.l1 a.l3) a.l0 a.l3) a.l1 a.l2)) a.l2 a.l2,
    .mad true (.add (.mad true (.mad true (.mad false (.mad false (.lit 0 0 0 0) a.l1 a.l4) a.l2 a.l3) a.l0 a.l4) a.l1 a.l3) (.mad true (.mad true (.mad false (.mad false (.lit 0 0 0 0) a.l1 a.l4) a.l2 a.l3) a.l0 a.l4) a.l1 a.l3)) a.l2 a.l2,
    .mad false (.add (.mad true (.mad true (.mad false (.lit 0 0 0 0) a.l2 a.l4) a.l1 a.l4) a.l2 a.l3) (.mad true (.mad true (.mad false (.lit 0 0 0 0) a.l2 a.l4) a.l1 a.l4) a.l2 a.l3)) a.l3 a.l3,
    .mad true (.add (.mad true (.mad false (.lit 0 0 0 0) a.l3 a.l4) a.l2 a.l4) (.mad true (.mad false (.lit 0 0 0 0) a.l3 a.l4) a.l2 a.l4)) a.l3 a.l3,
    .mad false (.add (.mad true (.lit 0 0 0 0) a.l3 a.l4) (.mad true (.lit 0 0 0 0) a.l3 a.l4)) a.l4 a.l4,
    .mad true (.lit 0 0 0 0) a.l4 a.l4]

theorem sqrCols_eq (a : F5 T) : Id.run (sqrCols tops a) = sqrColsT a := by
  have rep : List.replicate 9 (none : Option T) = [none, none, none, none, none, none, none, none, none] := rfl
  have r17 : List.range' 1 7 = [1, 2, 3, 4, 5, 6, 7] := by decide
  simp only [sqrCols, range5, range10, r17, rep, Id.run, bind, pure, List.foldlM_cons, List.foldlM_nil, List.mapM_cons,
    List.mapM_nil, List.getD_cons_zero, List.getD_cons_succ, List.set_cons_zero, List.set_cons_succ, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMod, Nat.reduceDiv, Nat.reduceBEq,
    F5.get, tops, Option.getD_some, Option.getD_none, sqrColsT, and_self, and_true, and_false, ↓reduceIte,
    List.getD_nil]

theorem mulCols_int (a b : F5 T) (E : Env) (k : Nat) :
    (mulColsT a b).map (fun t => t.int E k) = mulColsI (a.l0.int E k) (a.l1.int E k) (a.l2.int E k) (a.l3.int E k) (a.l4.int E k) (b.l0.int E k) (b.l1.int E k) (b.l2.int E k) (b.l3.int E k) (b.l4.int E k) := by
  have z : ((0 : Nat) : Int) = 0 := rfl
  simp only [mulColsT, List.map_cons, List.map_nil, T.int, pick4_same, z, mulColsI, lo52, hi52]

theorem sqrCols_int (a : F5 T) (E : Env) (k : Nat) :
    (sqrColsT a).map (fun t => t.int E k) = sqrColsI (a.l0.int E k) (a.l1.int E k) (a.l2.int E k) (a.l3.int E k) (a.l4.int E k) := by
  have z : ((0 : Nat) : Int) = 0 := rfl
  simp only [sqrColsT, List.map_cons, List.map_nil, T.int, pick4_same, z, sqrColsI, lo52, hi52]

/-- The limbs of lane `k` are in `[0, 2⁵²)`. -/
def Carried (E : Env) (k : Nat) (v : F5 T) : Prop :=
  (0 ≤ v.l0.int E k ∧ v.l0.int E k < 2 ^ 52) ∧ (0 ≤ v.l1.int E k ∧ v.l1.int E k < 2 ^ 52) ∧
    (0 ≤ v.l2.int E k ∧ v.l2.int E k < 2 ^ 52) ∧ (0 ≤ v.l3.int E k ∧ v.l3.int E k < 2 ^ 52) ∧
    (0 ≤ v.l4.int E k ∧ v.l4.int E k < 2 ^ 52)

theorem reduceI_valL (t : List Int) (ht : t.length = 10) :
    let o := reduceI t
    ∃ M, 0 ≤ M ∧ M < 2 ^ 260 ∧ val5 o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2 * 2 ^ 260 = val10L t + M * pI := by
  match t, ht with
  | [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9], _ => exact reduceI_val t0 t1 t2 t3 t4 t5 t6 t7 t8 t9

theorem mulCore_li (a b : F5 T) (E : Env) (k : Nat) :
    li E k (Id.run (mulCore tops a b)) = reduceI ((mulColsT a b).map fun t => t.int E k) := by
  have := mulCols_eq a b
  simp only [Id.run] at this
  simp only [mulCore, Id.run, bind, this, mulColsT, List.map_cons, List.map_nil]
  exact reduce_int _ _ _ _ _ _ _ _ _ _ _ rfl E k

theorem sqrCore_li (a : F5 T) (E : Env) (k : Nat) :
    li E k (Id.run (sqrCore tops a)) = reduceI ((sqrColsT a).map fun t => t.int E k) := by
  have := sqrCols_eq a
  simp only [Id.run] at this
  simp only [sqrCore, Id.run, bind, this, sqrColsT, List.map_cons, List.map_nil]
  exact reduce_int _ _ _ _ _ _ _ _ _ _ _ rfl E k

theorem vI_li (E : Env) (k : Nat) (v : F5 T) :
    vI E k v = val5 (li E k v).1 (li E k v).2.1 (li E k v).2.2.1 (li E k v).2.2.2.1 (li E k v).2.2.2.2 := rfl

/-- A product of carried lanes, times `2²⁶⁰`, is the product of the numbers plus a multiple of `p`. -/
theorem mulCore_val (a b : F5 T) (E : Env) (k : Nat) (ha : Carried E k a) (hb : Carried E k b) :
    ∃ M, 0 ≤ M ∧ M < 2 ^ 260 ∧
      vI E k (Id.run (mulCore tops a b)) * 2 ^ 260 = vI E k a * vI E k b + M * pI := by
  obtain ⟨M, h0, h1, h2⟩ := reduceI_valL ((mulColsT a b).map fun t => t.int E k)
    (by simp only [mulColsT, List.map_cons, List.map_nil, List.length_cons, List.length_nil])
  rw [mulCols_int, mulColsI_val ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1
    hb.2.2.2.2, ← mulCols_int, ← mulCore_li] at h2
  rw [vI_li]
  exact ⟨M, h0, h1, h2⟩

/-- A square of carried lanes, likewise. -/
theorem sqrCore_val (a : F5 T) (E : Env) (k : Nat) (ha : Carried E k a) :
    ∃ M, 0 ≤ M ∧ M < 2 ^ 260 ∧
      vI E k (Id.run (sqrCore tops a)) * 2 ^ 260 = vI E k a * vI E k a + M * pI := by
  obtain ⟨M, h0, h1, h2⟩ := reduceI_valL ((sqrColsT a).map fun t => t.int E k)
    (by simp only [sqrColsT, List.map_cons, List.map_nil, List.length_cons, List.length_nil])
  rw [sqrCols_int, sqrColsI_val ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2, ← sqrCols_int, ← sqrCore_li] at h2
  rw [vI_li]
  exact ⟨M, h0, h1, h2⟩

end


open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (sel4)

theorem blendOf_lanes : ∀ m < 16, blendOf (klit (K4.lanes m)) = some m := by decide

theorem maskOf_lanes : ∀ m < 16, maskOf (klit (K4.lanes m)) =
    some (if m.testBit 0 then 64 else 0, if m.testBit 1 then 64 else 0, if m.testBit 2 then 64 else 0,
      if m.testBit 3 then 64 else 0) := by decide

theorem tops_blend (a b : T) {m : Nat} (hm : m < 16) : tops.blend a b m = .blend a b m := by
  simp only [tops, selOf, blendOf_lanes m hm]

theorem tops_andl (a : T) {m : Nat} (hm : m < 16) :
    tops.andc a (K4.lanes m) = .mask a (if m.testBit 0 then 64 else 0) (if m.testBit 1 then 64 else 0)
      (if m.testBit 2 then 64 else 0) (if m.testBit 3 then 64 else 0) := by
  simp only [tops, maskOf_lanes m hm]

/-- A term masked to the lanes of `m`. -/
theorem andl_int (a : T) {m : Nat} (hm : m < 16) (E : Env) {k : Nat} (hk : k < 4) :
    (tops.andc a (K4.lanes m)).int E k = if m.testBit k then a.int E k else 0 := by
  rw [tops_andl a hm]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp only [T.int, pick4] <;> split <;>
    simp_all [Int.emod_one]

theorem vI_fadd (a b : F5 T) (E : Env) (k : Nat) : vI E k (fadd tops a b) = vI E k a + vI E k b := by
  simp only [fadd, F5.zipM, bind, pure, tops, vI, T.int, val5]
  omega

theorem vI_fsub (a b : F5 T) (E : Env) (k : Nat) : vI E k (fsub tops a b) = vI E k a - vI E k b := by
  simp only [fsub, F5.zipM, bind, pure, tops, vI, T.int, val5]
  omega

theorem vI_fshl (a : F5 T) (n : Nat) (E : Env) (k : Nat) :
    vI E k (fshl tops a n) = vI E k a * 2 ^ n := by
  by_cases h : n = 1
  · subst h
    simp only [fshl, F5.mapM, bind, pure, tops, vI, T.int, val5, ↓reduceIte]
    omega
  · simp only [fshl, F5.mapM, bind, pure, tops, vI, T.int, val5, h, ↓reduceIte]
    generalize (2 : Int) ^ n = w
    grind

theorem vI_fperm (a : F5 T) (i0 i1 i2 i3 : Nat) (E : Env) (k : Nat) :
    vI E k (fperm tops a i0 i1 i2 i3) = vI E (sel4 (i0 + 4 * i1 + 16 * i2 + 64 * i3) k) a := by
  simp only [fperm, F5.mapM, bind, pure, tops, vI, T.int]

theorem vI_fblend (a b : F5 T) {m : Nat} (hm : m < 16) (E : Env) (k : Nat) :
    vI E k (fblend tops a b m) = if m.testBit k then vI E k b else vI E k a := by
  simp only [fblend, F5.zipM, bind, pure, tops_blend _ _ hm, vI, T.int]
  split <;> rfl

theorem vI_fmadd (acc b : F5 T) {m : Nat} (hm : m < 16) (E : Env) {k : Nat} (hk : k < 4) :
    vI E k (fmadd tops acc b m) = vI E k acc + if m.testBit k then vI E k b else 0 := by
  have e (x y : T) : (tops.add x (tops.andc y (K4.lanes m))).int E k =
      x.int E k + if m.testBit k then y.int E k else 0 := by
    rw [← andl_int y hm E hk]; rfl
  simp only [fmadd, F5.zipM, bind, pure, vI, e, val5]
  split <;> omega

theorem vI_fmsub (acc b : F5 T) {m : Nat} (hm : m < 16) (E : Env) {k : Nat} (hk : k < 4) :
    vI E k (fmsub tops acc b m) = vI E k acc - if m.testBit k then vI E k b else 0 := by
  have e (x y : T) : (tops.sub x (tops.andc y (K4.lanes m))).int E k =
      x.int E k - if m.testBit k then y.int E k else 0 := by
    rw [← andl_int y hm E hk]; rfl
  simp only [fmsub, F5.zipM, bind, pure, vI, e, val5]
  split <;> omega

theorem vI_fmrsub (acc a : F5 T) {m : Nat} (hm : m < 16) (E : Env) (k : Nat) :
    vI E k (fmrsub tops acc a m) = if m.testBit k then vI E k a - vI E k acc else vI E k acc := by
  have e (x y : T) : (tops.blend x (tops.sub y x) m).int E k =
      if m.testBit k then y.int E k - x.int E k else x.int E k := by
    rw [tops_blend _ _ hm]; rfl
  simp only [fmrsub, F5.zipM, bind, pure, vI, e, val5]
  split <;> omega

theorem limbOf_val (v : Nat) :
    val5 (limbOf v 0 : Nat) (limbOf v 1 : Nat) (limbOf v 2 : Nat) (limbOf v 3 : Nat) (limbOf v 4 : Nat) = (v : Int) := by
  simp only [limbOf, val5, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceMul]
  omega

theorem pN_eq : (pN : Int) = pI := by decide

theorem vI_fbias (a : F5 T) (k0 k1 k2 k3 : Nat) (E : Env) {k : Nat} (hk : k < 4) :
    vI E k (fbias tops a k0 k1 k2 k3) = vI E k a + (pick4 k0 k1 k2 k3 k : Nat) * pI := by
  have e (x : T) (i : Nat) : (tops.addc x (biasK k0 k1 k2 k3 i)).int E k =
      x.int E k + (limbOf (pick4 k0 k1 k2 k3 k * pN) i : Nat) := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
  have := limbOf_val (pick4 k0 k1 k2 k3 k * pN)
  rw [Int.natCast_mul, pN_eq] at this
  simp only [fbias, bind, pure, vI, e]
  simp only [val5] at this ⊢
  omega

theorem vI_fneg (a : F5 T) (E : Env) (k : Nat) : vI E k (fneg tops a) = -vI E k a := by
  have z : ((0 : Nat) : Int) = 0 := rfl
  simp only [fneg, F5.mapM, bind, pure, tops, vI, T.int, pick4_same, z, val5]
  omega

theorem vI_fsel (c : T) (hc : blendOf c = none) (a b : F5 T) (E : Env) (k : Nat) :
    vI E k (fsel tops c a b) = if c.int E k = 0 then vI E k a else vI E k b := by
  simp only [fsel, F5.zipM, bind, pure, tops, selOf, hc, vI, T.int]
  split <;> rfl

/-- The simp set that evaluates the number of a lane of sums, differences and choices of field vectors. -/
macro "glue_simp" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [$ds,*, Id.run, bind, pure, vI_fbias, vI_fblend, vI_fmadd, vI_fmsub, vI_fmrsub, vI_fperm,
    vI_fshl, vI_fadd, vI_fsub, sel4, pick4, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.reduceDiv,
    Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceBEq, Nat.reduceBNe,
    Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd, Bool.false_eq_true,
    reduceCtorEq])

/-! ## `norm` -/

theorem iv_add_right {B : Bnds} {a b : T} {k : Nat} {iv : Int × Int} (h : (T.add a b).iv B k = some iv) :
    ∃ y, b.iv B k = some y := by
  simp only [T.iv, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, _, y, hy, _⟩ := h
  exact ⟨y, hy⟩

theorem iv_sra {B : Bnds} {a : T} {n k : Nat} {iv : Int × Int} (h : (T.sra a n).iv B k = some iv) :
    ∃ x, a.iv B k = some x ∧ -2 ^ 63 ≤ x.1 ∧ x.2 < 2 ^ 63 := by
  simp only [T.iv, Option.bind_eq_some_iff] at h
  obtain ⟨x, hx, h⟩ := h
  split at h
  · rename_i hr; exact ⟨x, hx, hr⟩
  · cases h

/-- What the last carry of `norm` is taken from. -/
def normY3 (v : F5 T) : T :=
  .add (.sub v.l3 (.shl (.sra v.l4 48) 36))
    (.sra (.add v.l2 (.sra (.add (.sub v.l1 (.shl (.sra v.l4 48) 44)) (.sra (.add v.l0 (.sra v.l4 48)) 52)) 52)) 52)

theorem norm_l4 (v : F5 T) :
    (Id.run (norm tops v)).l4 = .add (.add (.mask v.l4 48 48 48 48) (.shl (.sra v.l4 48) 16)) (.sra (normY3 v) 52) := by
  simp only [norm, Id.run, bind, pure, tops, maskOf_m48, normY3]

/-- `norm` of a lane whose number is in `[0, 2²⁶⁸)` and whose top limb has
bounds: carried, the number less a multiple of `p`, below `2²⁵⁶ + 2²³⁸`. -/
theorem norm_carried {s₀ : State} {B : Bnds} (hB : EnvOK s₀ B) (v : F5 T) {k : Nat} (hk : k < 4) {iv : Int × Int}
    (h : (Id.run (norm tops v)).l4.iv B k = some iv)
    (h0 : 0 ≤ vI (envOf s₀) k v) (h1 : vI (envOf s₀) k v < 2 ^ 268) :
    Carried (envOf s₀) k (Id.run (norm tops v)) ∧
      vI (envOf s₀) k (Id.run (norm tops v)) = vI (envOf s₀) k v - v.l4.int (envOf s₀) k / 2 ^ 48 * pI ∧
      0 ≤ vI (envOf s₀) k (Id.run (norm tops v)) ∧ vI (envOf s₀) k (Id.run (norm tops v)) < 2 ^ 256 + 2 ^ 238 := by
  rw [norm_l4] at h
  obtain ⟨y, hy⟩ := iv_add_right h
  obtain ⟨x, hx, r0, r1⟩ := iv_sra hy
  obtain ⟨-, lo, hi⟩ := iv_ok hB (normY3 v) k x hk hx
  have r3 : -2 ^ 63 ≤ (normY3 v).int (envOf s₀) k ∧ (normY3 v).int (envOf s₀) k < 2 ^ 63 := ⟨by omega, by omega⟩
  simp only [normY3, T.int] at r3
  have := normI_carried r3 h0 h1
  rw [← norm_int] at this
  exact this

end VG.Proof.P256.X86_64.Ifma
