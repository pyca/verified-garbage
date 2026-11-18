module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.VNtt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.PPC64LE.VWords
public import VerifiedGarbage.Proof.MlDsa.Arith.Zq

/-! ### `MlDsa.PPC64LE.VNtt.Mem`, which this module and modules that import it used -/

section

/-! ### `MlDsa.PPC64LE.VNtt.Lanes`, which this module and modules that import it used -/

section

/-!
# ML-DSA's vector NTT on PPC64LE: lanes

The arithmetic of one lane of the butterfly (`bfly_lane`), on the words of
vectors of `Proof/Framework/PPC64LE/VWords.lean`: Shoup's product
(`shoup_lane`) and the reductions by `vminuw` (`minu_sub`, `minu_add_lane`,
`minu_sub_lane`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE

/-! ## Shoup's product -/

/-- Shoup: `hi = ⌊b·⌊z·2³²/q⌋/2³²⌋` gives `0 ≤ b·z − hi·q < 2q`. -/
theorem shoup_bounds {q b z : Nat} (hq : 0 < q) (hb : b < 2^32) :
    (b * (z * 2^32 / q) / 2^32) * q ≤ b * z ∧
    b * z < (b * (z * 2^32 / q) / 2^32) * q + 2 * q := by
  have e1 : z * 2^32 / q * q ≤ z * 2^32 := Nat.div_mul_le_self _ _
  have e2 : z * 2^32 < z * 2^32 / q * q + q := Nat.lt_div_mul_add hq
  have h1 : b * (z * 2^32 / q) / 2^32 * 2^32 ≤ b * (z * 2^32 / q) := Nat.div_mul_le_self _ _
  have h2 : b * (z * 2^32 / q) < b * (z * 2^32 / q) / 2^32 * 2^32 + 2^32 := Nat.lt_div_mul_add (by decide)
  generalize z * 2^32 / q = z' at *
  generalize b * z' / 2^32 = hi at *
  constructor
  · apply Nat.le_of_mul_le_mul_right (c := 2^32) _ (by decide)
    calc hi * q * 2^32 = hi * 2^32 * q := Nat.mul_right_comm _ _ _
      _ ≤ b * z' * q := Nat.mul_le_mul_right _ h1
      _ = b * (z' * q) := Nat.mul_assoc _ _ _
      _ ≤ b * (z * 2^32) := Nat.mul_le_mul_left _ e1
      _ = b * z * 2^32 := (Nat.mul_assoc _ _ _).symm
  · apply Nat.lt_of_mul_lt_mul_right (a := 2^32)
    have m1 : b * z' * q < (hi * 2^32 + 2^32) * q := Nat.mul_lt_mul_of_pos_right h2 hq
    have m2 : b * q < 2^32 * q := Nat.mul_lt_mul_of_pos_right hb hq
    calc b * z * 2^32 = b * (z * 2^32) := Nat.mul_assoc _ _ _
      _ ≤ b * (z' * q + q) := Nat.mul_le_mul_left _ (Nat.le_of_lt e2)
      _ = b * z' * q + b * q := by rw [Nat.mul_add, Nat.mul_assoc]
      _ < (hi * 2^32 + 2^32) * q + 2^32 * q := Nat.add_lt_add m1 m2
      _ = (hi * q + 2 * q) * 2^32 := by
        rw [Nat.add_mul, Nat.add_mul, Nat.mul_right_comm hi (2^32) q, Nat.mul_assoc 2 q,
          Nat.mul_comm q (2^32)]; omega_using []

/-- Reduce `r < 2q` to `r mod q`: `min(r, r − q)`. -/
theorem minu_sub {r qv : BitVec 32} (hq : 0 < qv.toNat) (hr : r.toNat < 2 * qv.toNat) (h2 : 2 * qv.toNat ≤ 2^32) :
    (minu32 r (r - qv)).toNat = r.toNat % qv.toNat := by
  unfold minu32
  have := r.isLt
  have hs := BitVec.toNat_sub r qv
  by_cases h : r.toNat < qv.toNat
  · rw [Nat.mod_eq_of_lt h, ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega_using [hs, h]), hs, show r.toNat % qv.toNat = r.toNat - qv.toNat from by
      rw [Nat.mod_eq_sub_mod (by omega_using [h]), Nat.mod_eq_of_lt (by omega_using [hr])]]
    omega_using [h]

/-- The Shoup product of one word lane: with `hi` the high word of `b·z'`,
`b·z − hi·q` modulo 2³², then `min` with that minus `q`. -/
theorem shoup_lane (b hi qv zv zpv : BitVec 32) (hq : 0 < qv.toNat) (hq2 : 2 * qv.toNat ≤ 2^32)
    (hzp : zpv.toNat = zv.toNat * 2^32 / qv.toNat) (hhi : hi.toNat = b.toNat * zpv.toNat / 2^32) :
    (minu32 (b * zv - hi * qv) (b * zv - hi * qv - qv)).toNat = b.toNat * zv.toNat % qv.toNat := by
  obtain ⟨l, u⟩ := shoup_bounds (q := qv.toNat) (z := zv.toNat) hq b.isLt
  rw [hzp] at hhi
  generalize b.toNat * (zv.toNat * 2^32 / qv.toNat) / 2^32 = h0 at l u hhi
  have hr : (b * zv - hi * qv).toNat = b.toNat * zv.toNat - h0 * qv.toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_mul, hhi]
    generalize b.toNat * zv.toNat = x at l u ⊢
    generalize h0 * qv.toNat = y at l u ⊢
    omega_using [hq2, l, u]
  rw [minu_sub hq (by omega_using [hq, u, hr]) hq2, hr,
    show b.toNat * zv.toNat = (b.toNat * zv.toNat - h0 * qv.toNat) + h0 * qv.toNat by omega_using [l],
    Nat.add_mul_mod_self_right, Nat.add_sub_cancel]

/-- `a + t` reduced: `min(s, s − q)`. -/
theorem minu_add_lane {a t qv : BitVec 32} (hq : 0 < qv.toNat) (hq2 : 2 * qv.toNat ≤ 2^32)
    (ha : a.toNat < qv.toNat) (ht : t.toNat < qv.toNat) :
    (minu32 (a + t) (a + t - qv)).toNat = (a.toNat + t.toNat) % qv.toNat := by
  have hs : (a + t).toNat = a.toNat + t.toNat := by rw [BitVec.toNat_add]; omega_using [hq2, ha, ht]
  rw [minu_sub hq (by omega_using [ha, ht, hs]) hq2, hs]

/-- `a − t` reduced: `min(d, d + q)`. -/
theorem minu_sub_lane {a t qv : BitVec 32} (hq2 : 2 * qv.toNat ≤ 2^32)
    (ha : a.toNat < qv.toNat) (ht : t.toNat < qv.toNat) :
    (minu32 (a - t) (a - t + qv)).toNat = (a.toNat + (qv.toNat - t.toNat)) % qv.toNat := by
  unfold minu32
  have hd := BitVec.toNat_sub a t
  have hd2 := BitVec.toNat_add (a - t) qv
  by_cases h : t.toNat ≤ a.toNat
  · rw [ite_eq_left (by omega_using [hq2, ha, hd, hd2, h]), hd]
    rw [show (a.toNat + (qv.toNat - t.toNat)) % qv.toNat = a.toNat - t.toNat from by
      rw [Nat.mod_eq_sub_mod (by omega_using [h]), Nat.mod_eq_of_lt (by omega_using [ha])]; omega_using [ha]]
    omega_using [h]
  · rw [ite_eq_right (by omega_using [ht, hd, hd2, h]), hd2, hd, Nat.mod_eq_of_lt (by omega_using [ha, h] : a.toNat + (qv.toNat - t.toNat) < qv.toNat)]
    omega_using [hq2, ha, ht]

open VG.Spec.MlDsa (q Zq)
open VG.Proof.MlDsa.Arith (val_add' val_sub' val_mul val_lt)

/-- One lane of the butterfly: `(a + z·b, a − z·b)`, with `hi` the high word
of `b·z'`. -/
theorem bfly_lane (a b hi qv zv zpv : BitVec 32) (x y z : Zq) (hqv : qv.toNat = q)
    (hzv : zv.toNat = z.val) (hzp : zpv.toNat = z.val * 2^32 / q) (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hhi : hi.toNat = b.toNat * zpv.toNat / 2^32) :
    let t := minu32 (b * zv - hi * qv) (b * zv - hi * qv - qv)
    (minu32 (a + t) (a + t - qv)).toNat = (x + z * y).val ∧
    (minu32 (a - t) (a - t + qv)).toNat = (x - z * y).val := by
  intro t
  have hq : 0 < qv.toNat := by rw [hqv]; decide
  have hq2 : 2 * qv.toNat ≤ 2^32 := by rw [hqv]; decide
  have ht : t.toNat = (z * y).val := by
    rw [shoup_lane b hi qv zv zpv hq hq2 (by rw [hzp, hzv, hqv]) hhi, val_mul, hb, hzv, hqv, Nat.mul_comm]
  have hax : a.toNat < qv.toNat := by rw [ha, hqv]; exact x.isLt
  have htx : t.toNat < qv.toNat := by rw [ht, hqv]; exact (z * y).isLt
  constructor
  · rw [minu_add_lane hq hq2 hax htx, val_add', ha, ht, hqv]
  · rw [minu_sub_lane hq2 hax htx, val_sub', ha, ht, hqv]

/-- One lane of the inverse butterfly: `a + b`, and `z·(b − a)` with
`d = b − a` reduced first. -/
theorem ibfly_lane (a b hi qv zv zpv : BitVec 32) (x y z : Zq) (hqv : qv.toNat = q)
    (hzv : zv.toNat = z.val) (hzp : zpv.toNat = z.val * 2^32 / q) (ha : a.toNat = x.val) (hb : b.toNat = y.val)
    (hhi : hi.toNat = (minu32 (b - a) (b - a + qv)).toNat * zpv.toNat / 2^32) :
    (minu32 (a + b) (a + b - qv)).toNat = (x + y).val ∧
    (minu32 (minu32 (b - a) (b - a + qv) * zv - hi * qv) (minu32 (b - a) (b - a + qv) * zv - hi * qv - qv)).toNat =
      (z * (y - x)).val := by
  have hq : 0 < qv.toNat := by rw [hqv]; decide
  have hq2 : 2 * qv.toNat ≤ 2^32 := by rw [hqv]; decide
  have hax : a.toNat < qv.toNat := by rw [ha, hqv]; exact x.isLt
  have hbx : b.toNat < qv.toNat := by rw [hb, hqv]; exact y.isLt
  have hd : (minu32 (b - a) (b - a + qv)).toNat = (y - x).val := by
    rw [minu_sub_lane hq2 hbx hax, val_sub', ha, hb, hqv]
  constructor
  · rw [minu_add_lane hq hq2 hax hbx, val_add', ha, hb, hqv]
  · rw [shoup_lane _ hi qv zv zpv hq hq2 (by rw [hzp, hzv, hqv]) hhi, val_mul, hd, hzv, hqv, Nat.mul_comm]

/-- One lane of a product by `z`: Shoup's, reduced. -/
theorem smul_lane (a hi qv zv zpv : BitVec 32) (x z : Zq) (hqv : qv.toNat = q)
    (hzv : zv.toNat = z.val) (hzp : zpv.toNat = z.val * 2^32 / q) (ha : a.toNat = x.val)
    (hhi : hi.toNat = a.toNat * zpv.toNat / 2^32) :
    (minu32 (a * zv - hi * qv) (a * zv - hi * qv - qv)).toNat = (z * x).val := by
  have hq : 0 < qv.toNat := by rw [hqv]; decide
  have hq2 : 2 * qv.toNat ≤ 2^32 := by rw [hqv]; decide
  rw [shoup_lane _ hi qv zv zpv hq hq2 (by rw [hzp, hzv, hqv]) hhi, val_mul, ha, hzv, hqv, Nat.mul_comm]

end VG.Proof.MlDsa.PPC64LE.VNtt

end

end

/-! # ML-DSA's vector NTT on PPC64LE: vectors of coefficients in memory

Coefficients `j … j+3` loaded by `lxvd2x` (`vword_loadC`) and stored by
`stxvd2x` (`coeffAt_store`), from the order of `vword_load` and
`readW_store` (`Proof/Framework/PPC64LE/VWords.lean`). -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE

/-! ## Coefficients -/

open VG.Proof.MlDsa (coeffAt PolyIs)
open VG.Proof.MlDsa.Arith (coeffAddr coeffAddr_add coeffAt_eq polyRegion polyIs_of_toNat polyIs_toNat)
open VG.Spec.MlDsa (Poly n)

/-- Lane `e` of a load of coefficients `j … j+3`. -/
theorem vword_loadC (m : Mem) (p : Addr) (j : Nat) {e : Nat} (he : e < 4) :
    vword (swapDwords (m.read (coeffAddr p j) 16)) e = coeffAt m p (j + (e ^^^ 1)) := by
  rw [vword_load _ _ he, coeffAddr_add, ← coeffAt_eq]

/-- Coefficient `i` after a store of `v` to coefficients `j … j+3`. -/
theorem coeffAt_store (m : Mem) (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) (v : BitVec 128) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.write (coeffAddr p j) 16 (swapDwords v)) p i =
      if j ≤ i ∧ i < j + 4 then vword v ((i - j) ^^^ 1) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [coeffAddr_add, show j + (i - j) = i by omega_using [h]]]
    exact readW_store _ _ _ (by omega_using [h])
  · have hw : m.write (coeffAddr p j) 16 (swapDwords v) = m.writeW (coeffAddr p j) (swapDwords v) := by
      simp only [Mem.writeW, BitVec.setWidth_eq]
    rw [hw]
    exact Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_using [hi]) (by omega_using [hj])) (by decide)

theorem vector_contains (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) :
    (polyRegion p).Contains (coeffAddr p j) 16 := Offset.contains_base p (by omega_using [hj]) (by omega_using [hj])

theorem frame_store2 {m m' : Mem} {p : Addr} (hf : Frame [polyRegion p] m m') {j j' : Nat}
    (hj : j + 4 ≤ 256) (hj' : j' + 4 ≤ 256) (x y : BitVec 128) :
    Frame [polyRegion p] m ((m'.write (coeffAddr p j) 16 x).write (coeffAddr p j') 16 y) :=
  (hf.write (List.mem_singleton_self _) x (vector_contains p hj)).write
    (List.mem_singleton_self _) y (vector_contains p hj')

/-- Two stores of vectors of coefficients, at `j` and at `j'`. -/
theorem polyIs_store2 {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P)
    {j j' : Nat} (hj : j + 4 ≤ 256) (hj' : j' + 4 ≤ 256)
    {x y : BitVec 128} (hx : ∀ e < 4, (vword x e).toNat = (R[j + (e ^^^ 1)]!).val)
    (hy : ∀ e < 4, (vword y e).toNat = (R[j' + (e ^^^ 1)]!).val)
    (hR : ∀ i < 256, ¬(j ≤ i ∧ i < j + 4) → ¬(j' ≤ i ∧ i < j' + 4) → R[i]! = P[i]!) :
    PolyIs ((m.write (coeffAddr p j) 16 (swapDwords x)).write (coeffAddr p j') 16 (swapDwords y)) p R :=
  polyIs_of_toNat fun i hi => by
    have hi' : i < 256 := hi
    rw [coeffAt_store _ _ hj' _ hi', coeffAt_store _ _ hj _ hi']
    by_cases h1 : j' ≤ i ∧ i < j' + 4
    · rw [ite_eq_left h1, hy _ (xor1_lt (by omega_using [h1])), xor1_xor1, show j' + (i - j') = i by omega_using [h1]]
    · rw [ite_eq_right h1]
      by_cases h2 : j ≤ i ∧ i < j + 4
      · rw [ite_eq_left h2, hx _ (xor1_lt (by omega_using [h2])), xor1_xor1, show j + (i - j) = i by omega_using [h2]]
      · rw [ite_eq_right h2, hR i hi' h2 h1, polyIs_toNat hP hi]

end VG.Proof.MlDsa.PPC64LE.VNtt

end

end

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
  omega_using [this]

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
  omega_using [hnz]

/-! ## Positions -/

theorem flip_eq {e : Nat} (he : e < 4) : swap1 e = e ^^^ 1 := by
  rcases (by omega_using [he] : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem flip_lt {e : Nat} (he : e < 4) : swap1 e < 4 := by unfold swap1; split <;> omega_arith

theorem scrK_wide {k : Nat} (h : k < 64) : scrK k = k := by
  unfold scrK; rw [ite_eq_left h]

theorem scrK_two {g r : Nat} (hg : g < 16) (hr : r < 4) : scrK (64 + 4 * g + swap1 r) = 64 + 4 * g + r := by
  unfold scrK swap1
  rw [ite_eq_right (by split <;> omega_using []), ite_eq_left (by split <;> omega_arith)]
  split <;> split <;> omega_arith

theorem scrK_even {g r : Nat} (hg : g < 16) (hr : r < 4) :
    scrK (128 + 8 * g + swap1 r) = 128 + 8 * g + 2 * r := by
  unfold scrK swap1
  rw [ite_eq_right (by split <;> omega_using []), ite_eq_right (by split <;> omega_using []), ite_eq_left (by split <;> omega_arith)]
  split <;> split <;> omega_arith

theorem scrK_odd {g r : Nat} (hg : g < 16) (hr : r < 4) :
    scrK (132 + 8 * g + swap1 r) = 128 + 8 * g + 2 * r + 1 := by
  unfold scrK swap1
  rw [ite_eq_right (by split <;> omega_using []), ite_eq_right (by split <;> omega_using []), ite_eq_right (by split <;> omega_arith)]
  split <;> split <;> omega_arith

theorem scrK_lt {p : Nat} (hp : p < 256) : scrK p < 256 := by
  unfold scrK swap1; repeat' split
  all_goals omega_arith

/-! ## Storing the table -/

theorem loadImm_lo_bits (a b : BitVec 16) :
    ((a ++ (0 : BitVec 16)).signExtend 64 ||| b.setWidth 64).setWidth 32 = a ++ b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_signExtend, BitVec.getLsbD_append, hi,
    decide_true, Bool.true_and, show i < 64 by omega_using [hi]]
  by_cases h : i < 16
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge b i (by omega_using [h])]

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
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun p hp hp' => absurd hp' (by omega_using [hp])⟩
  have hv := shoup_lt (zeta_lt (K (k + 1)))
  let s₁ := s.write .r12 ((BitVec.ofNat 16 (shoup (zeta (K (k + 1))) / 65536) ++ (0 : BitVec 16)).signExtend 64)
  let s₂ := s₁.write .r12 (s₁.gpr .r12 ||| (BitVec.ofNat 16 (shoup (zeta (K (k + 1))) % 65536)).setWidth 64)
  have v2 : (s₂.gpr .r12).setWidth 32 = BitVec.ofNat 32 (shoup (zeta (K (k + 1)))) := by
    simp only [s₂, s₁, State.write, ite_true]; exact loadImm_lo hv
  have e : s₂.gpr .r4 + BitVec.ofNat 64 (4 * (k + 1)) = s₀.gpr .r4 + BitVec.ofNat 64 (4 * (k + 1)) := by
    simp only [s₂, s₁, State.write, reduceCtorEq, ite_false, h.gpr .r4 (by decide)]
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_store_w (by decide) (show 4 * (k + 1) < 2 ^ 15 by omega_using [hk])
    (by show InRegions s₂.wr _ 4; rw [e]; exact h.wr ▸ hwr (k + 1) (by omega_using [hk]))) (wp_nil ?_)))
  show FillInv K s₀ (k + 1)
    { s₂ with mem := (s₂.mem.writeW (s₂.gpr .r4 + BitVec.ofNat 64 (4 * (k + 1))) ((s₂.gpr .r12).setWidth 32)) }
  rw [e, v2]
  refine ⟨fun r hr => ?_, h.vpr, h.rd, h.wr, h.sp, h.lr, h.syms, ?_, fun p hp hp' => ?_⟩
  · simp only [s₂, s₁, State.write, hr, ite_false]; exact h.gpr r hr
  · exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))
  · show (s.mem.writeW _ _).readW _ 32 = _
    by_cases ep : p = k + 1
    · subst ep; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [ep]) (by omega_using [hk, hp']) (by omega_using [hk])) (by decide)]
      exact h.tab p hp (by omega_using [hp', ep])

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
    split <;> first | omega | exact congrArg _ (by omega_using [])

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
      omega_using [h1]
    rw [show (BitVec.ofInt 32 1).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega_using [hs])]
    exact zrec (hz i hi)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.MlDsa.PPC64LE.VNtt
