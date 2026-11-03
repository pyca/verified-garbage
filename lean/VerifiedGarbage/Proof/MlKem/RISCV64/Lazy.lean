module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Reduce
public import VerifiedGarbage.Proof.MlKem.Blocks
public import VerifiedGarbage.Proof.MlKem.NttLayer
public import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-KEM on RISC-V: the lazy butterflies' values

As ML-DSA's on RISC-V (`Proof/MlDsa/RISCV64/Arith/Lazy.lean`), for
`q = 3329`: `barrettM` leaves `barM x = x - ⌊x · m / 2⁶⁴⌋ · q` for
`m = ⌊2⁶⁴ / q⌋`, less than `2q` and congruent to `x` for every `x` (`barM_lt`,
`barM_mod`), and `reduceM` leaves `x mod q` (`redM_toNat`).

* `opB` is what the forward butterfly stores, `(x + t, x − t + 2q)` for the
  reduced product `t` of `y` and the zeta, computed on 64 bits and stored as
  the low word; for `x < 13 q` it is that sum and difference, less than `2q`
  more than `x` and congruent to the specification's butterfly, so a layer
  takes `Rel b` to `Rel (b + 2)` (`layerB_rel`), and seven layers from
  `Rel 1` end at `Rel 15`.
* `opIB` is the inverse butterfly's, `(x + y, t)` for the reduced product
  `t` of the zeta and `y − x + 64 q`: for `x, y < b q` with `b ≤ 64`, a layer
  takes `Rel b` to `Rel 2b` (`layerIB_rel`), and seven layers from `Rel 1`
  end at `Rel 128`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Lazy

open VG VG.RISCV64
open VG.Spec.MlKem
open VG.Proof.MlKem (wbfly wBlockN wBlk_ok layF layF_get n_eq q_eq)

/-! ## Barrett reduction on 64 bits -/

/-- `m = ⌊2⁶⁴ / q⌋`, and `m q + 2988 = 2⁶⁴`. -/
theorem m_q : 5541226816974932 * q + 2988 = 2 ^ 64 := by rw [q_eq]

/-- The quotient's estimate, `⌊x · m / 2⁶⁴⌋`, as `mulhu` computes it. -/
def barQ (x : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (x.toNat * 5541226816974932 / 2 ^ 64)

theorem bar_spec (x : Nat) (hx : x < 2 ^ 64) :
    x * 5541226816974932 / 2 ^ 64 * q ≤ x ∧ x < x * 5541226816974932 / 2 ^ 64 * q + 2 * q := by
  have hd := Nat.div_add_mod (x * 5541226816974932) (2 ^ 64)
  have hr := Nat.mod_lt (x * 5541226816974932) (show 0 < 2 ^ 64 by decide)
  generalize x * 5541226816974932 / 2 ^ 64 = T at *
  generalize x * 5541226816974932 % 2 ^ 64 = R at *
  have key : x * 2 ^ 64 = T * q * 2 ^ 64 + (R * q + 2988 * x) := by
    have := m_q
    calc x * 2 ^ 64 = x * (5541226816974932 * q + 2988) := by rw [this]
      _ = (x * 5541226816974932) * q + 2988 * x := by rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm 2988 x]
      _ = (2 ^ 64 * T + R) * q + 2988 * x := by rw [hd]
      _ = T * q * 2 ^ 64 + (R * q + 2988 * x) := by
        rw [Nat.add_mul, Nat.add_assoc, Nat.mul_comm (2 ^ 64) T, Nat.mul_right_comm T (2 ^ 64) q]
  have hq : 2988 < q := by rw [q_eq]; decide
  generalize q = Q at *
  have e1 : R * Q < 2 ^ 64 * Q := Nat.mul_lt_mul_of_pos_right hr (by omega)
  have e2 : 2988 * x < Q * 2 ^ 64 := Nat.mul_lt_mul_of_le_of_lt (by omega) hx (by omega)
  have hle : T * Q ≤ x :=
    Nat.le_of_mul_le_mul_right (show T * Q * 2 ^ 64 ≤ x * 2 ^ 64 by omega) (Nat.two_pow_pos 64)
  have h2 : x * 2 ^ 64 < T * Q * 2 ^ 64 + 2 * Q * 2 ^ 64 := by omega
  rw [← Nat.add_mul] at h2
  exact ⟨hle, Nat.lt_of_mul_lt_mul_right h2⟩

/-- What `barrettM d t` leaves in `d`. -/
def barM (x : BitVec 64) : BitVec 64 := x - barQ x * 3329

theorem barM_toNat (x : BitVec 64) :
    (barM x).toNat = x.toNat - x.toNat * 5541226816974932 / 2 ^ 64 * q := by
  obtain ⟨hle, -⟩ := bar_spec x.toNat x.isLt
  have hx := x.isLt
  have hT : (barQ x).toNat = x.toNat * 5541226816974932 / 2 ^ 64 := by
    unfold barQ; rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by rw [q_eq] at hle; omega)
  unfold barM
  generalize barQ x = B at hT ⊢
  generalize x.toNat * 5541226816974932 / 2 ^ 64 = T at hle hT ⊢
  subst hT
  rw [q_eq] at hle ⊢
  have hm : (B * 3329).toNat = B.toNat * 3329 := by
    rw [BitVec.toNat_mul, show (3329 : BitVec 64).toNat = 3329 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hm]; omega), hm]

theorem barM_lt (x : BitVec 64) : (barM x).toNat < 2 * q := by
  obtain ⟨hle, hlt⟩ := bar_spec x.toNat x.isLt
  rw [barM_toNat]; omega

theorem barM_mod (x : BitVec 64) : (barM x).toNat % q = x.toNat % q := by
  obtain ⟨hle, -⟩ := bar_spec x.toNat x.isLt
  rw [barM_toNat]
  generalize x.toNat * 5541226816974932 / 2 ^ 64 = T at hle ⊢
  have e : x.toNat = (x.toNat - T * q) + q * T := by rw [Nat.mul_comm q T]; omega
  conv => rhs; rw [e]
  rw [Nat.add_mul_mod_self_left]

/-- What `reduceM d t` leaves in `d`. -/
def redM (x : BitVec 64) : BitVec 64 := fixq (barM x - 3329)

theorem redM_toNat (x : BitVec 64) : (redM x).toNat = x.toNat % q := by
  unfold redM
  rw [fixq_subq (barM_lt x), barM_mod]

/-! ## Words -/

/-- A coefficient as the code stores it. -/
abbrev Word := Fin 4294967296

/-- Words of a polynomial. -/
abbrev WPoly := Vector Word n

/-- A word on 64 bits. -/
abbrev w64 (x : Word) : BitVec 64 := BitVec.ofNat 64 x.val

/-- The low word of a value on 64 bits. -/
abbrev toW (v : BitVec 64) : Word := Fin.ofNat _ v.toNat

/-- A zeta on 64 bits. -/
abbrev z64 (z : Zq) : BitVec 64 := BitVec.ofNat 64 z.val

/-- The residue of a word. -/
abbrev residue (x : Word) : Zq := Fin.ofNat q x.val

theorem w64_toNat (x : Word) : (w64 x).toNat = x.val := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

/-! ## The forward butterfly -/

/-- The reduced product of `y` and the zeta. -/
def prod (y : Word) (z : Zq) : Nat := (barM (z64 z * w64 y)).toNat

theorem z64_mul (y : Word) (z : Zq) : (z64 z * w64 y).toNat = z.val * y.val := by
  have hz : z.val < 3329 := z.isLt
  have hy : y.val < 4294967296 := y.isLt
  have e1 : z.val % 2 ^ 64 = z.val := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_mul, w64_toNat, BitVec.toNat_ofNat, e1]
  have := Nat.mul_lt_mul_of_lt_of_le hz (Nat.le_of_lt hy) (by omega)
  exact Nat.mod_eq_of_lt (by omega)

theorem prod_lt (y : Word) (z : Zq) : prod y z < 2 * q := barM_lt _

theorem prod_mod (y : Word) (z : Zq) : prod y z % q = z.val * y.val % q := by
  rw [prod, barM_mod, z64_mul]

/-- What the forward butterfly stores: `x + t` and `x − t + 2q`, on 64 bits,
as words. -/
def opB (x y : Word) (z : Zq) : Word × Word :=
  (toW (w64 x + barM (z64 z * w64 y)), toW (w64 x - barM (z64 z * w64 y) + 6658))

theorem opB_values (x y : Word) (z : Zq) (hx : x.val < 13 * q) :
    (opB x y z).1.val = x.val + prod y z ∧ (opB x y z).2.val = x.val + 2 * q - prod y z := by
  have ht := prod_lt y z
  have hx' := w64_toNat x
  simp only [opB, toW, Fin.val_ofNat]
  unfold prod at ht ⊢
  generalize barM (z64 z * w64 y) = T at ht ⊢
  rw [q_eq] at hx ht ⊢
  constructor
  · rw [BitVec.toNat_add, hx', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · have e : (w64 x - T + 6658).toNat = x.val + 6658 - T.toNat := by
      generalize w64 x = X at hx' ⊢
      bv_omega
    rw [e, Nat.mod_eq_of_lt (by omega)]

theorem opB_bound (x y : Word) (z : Zq) {b : Nat} (hb : b ≤ 13) (hx : x.val < b * q) :
    (opB x y z).1.val < (b + 2) * q ∧ (opB x y z).2.val < (b + 2) * q := by
  have hv := opB_values x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb))
  have ht := prod_lt y z
  rw [hv.1, hv.2, Nat.add_mul]
  omega

theorem opB_residue (x y : Word) (z : Zq) (hx : x.val < 13 * q) :
    residue (opB x y z).1 = residue x + z * residue y ∧
    residue (opB x y z).2 = residue x - z * residue y := by
  have hv := opB_values x y z hx
  have ht := prod_lt y z
  have hm' : (z * residue y).val = prod y z % q := by
    rw [Fin.val_mul, residue, Fin.val_ofNat, Nat.mul_mod_mod, prod_mod]
  constructor
  · apply Fin.ext
    rw [Fin.val_add, hm']
    change (opB x y z).1.val % q = (x.val % q + prod y z % q) % q
    rw [hv.1, Nat.add_mod]
  · apply Fin.ext
    rw [Fin.val_sub, hm']
    change (opB x y z).2.val % q = (q - prod y z % q + x.val % q) % q
    rw [hv.2]
    have ht' : prod y z < 2 * 3329 := ht
    change (x.val + 2 * 3329 - prod y z) % 3329 = (3329 - prod y z % 3329 + x.val % 3329) % 3329
    omega

/-! ## The inverse butterfly -/

/-- The reduced product of the zeta and `y − x + 64 q`, on 64 bits. -/
def prodI (x y : Word) (z : Zq) : Nat := (barM (z64 z * (w64 y - w64 x + 213056))).toNat

/-- What the inverse butterfly stores: `x + y`, and the reduced product of
the zeta and `y − x + 64 q`, as words. -/
def opIB (x y : Word) (z : Zq) : Word × Word :=
  (toW (w64 x + w64 y), toW (barM (z64 z * (w64 y - w64 x + 213056))))

theorem opIB_values (x y : Word) (z : Zq) (hx : x.val < 64 * q) (hy : y.val < 64 * q) :
    (opIB x y z).1.val = x.val + y.val ∧ (opIB x y z).2.val = prodI x y z ∧
      prodI x y z < 2 * q ∧ prodI x y z % q = z.val * (y.val + 64 * q - x.val) % q := by
  have hx' := w64_toNat x
  have hy' := w64_toNat y
  have hz : z.val < 3329 := z.isLt
  rw [q_eq] at hx hy
  have hd : (w64 y - w64 x + 213056).toNat = y.val + 213056 - x.val := by
    generalize w64 x = X at hx' ⊢
    generalize w64 y = Y at hy' ⊢
    bv_omega
  have hp : (z64 z * (w64 y - w64 x + 213056)).toNat = z.val * (y.val + 213056 - x.val) := by
    have e1 : z.val % 2 ^ 64 = z.val := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_mul, hd, BitVec.toNat_ofNat, e1]
    have := Nat.mul_lt_mul_of_lt_of_le hz (show y.val + 213056 - x.val ≤ 2 ^ 19 by omega) (by omega)
    exact Nat.mod_eq_of_lt (by omega)
  have hl := barM_lt (z64 z * (w64 y - w64 x + 213056))
  rw [q_eq] at hl
  refine ⟨?_, ?_, by rw [q_eq]; exact hl, ?_⟩
  · simp only [opIB, toW, Fin.val_ofNat]
    rw [BitVec.toNat_add, hx', hy', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · simp only [opIB, toW, Fin.val_ofNat, prodI]
    exact Nat.mod_eq_of_lt (by omega)
  · have := barM_mod (z64 z * (w64 y - w64 x + 213056))
    rw [hp] at this
    exact this

theorem opIB_bound (x y : Word) (z : Zq) {b : Nat} (hb : 1 ≤ b) (hb' : b ≤ 64) (hx : x.val < b * q)
    (hy : y.val < b * q) : (opIB x y z).1.val < 2 * b * q ∧ (opIB x y z).2.val < 2 * b * q := by
  have hv := opIB_values x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb'))
    (Nat.lt_of_lt_of_le hy (Nat.mul_le_mul_right q hb'))
  rw [hv.1, hv.2.1, Nat.mul_assoc]
  constructor
  · omega
  · exact Nat.lt_of_lt_of_le hv.2.2.1 (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left q hb))

theorem opIB_residue (x y : Word) (z : Zq) (hx : x.val < 64 * q) (hy : y.val < 64 * q) :
    residue (opIB x y z).1 = residue x + residue y ∧
    residue (opIB x y z).2 = z * (residue y - residue x) := by
  have hv := opIB_values x y z hx hy
  constructor
  · apply Fin.ext
    rw [Fin.val_add]
    change (opIB x y z).1.val % q = (x.val % q + y.val % q) % q
    rw [hv.1, Nat.add_mod]
  · apply Fin.ext
    change (opIB x y z).2.val % q = (z * (residue y - residue x)).val
    rw [hv.2.1, hv.2.2.2, Fin.val_mul, Fin.val_sub, residue, residue, Fin.val_ofNat, Fin.val_ofNat]
    have hl : (y.val + 64 * q - x.val) % q = (q - x.val % q + y.val % q) % q := by
      rw [q_eq] at hx hy ⊢; omega
    rw [Nat.mul_mod, hl, Nat.mul_mod z.val ((q - x.val % q + y.val % q) % q), Nat.mod_mod]

/-! ## Layers -/

/-- Words bounded by `b q` whose residues are `f`'s. -/
def Rel (b : Nat) (F : WPoly) (f : Poly) : Prop :=
  ∀ i < 256, F[i]!.val < b * q ∧ residue F[i]! = f[i]!

/-- A polynomial's coefficients as words. -/
def lift (f : Poly) : WPoly := f.map fun x => ⟨x.val, Nat.lt_trans x.isLt (by decide)⟩

theorem lift_get (f : Poly) {i : Nat} (hi : i < 256) : ((lift f)[i]!).val = (f[i]!).val := by
  rw [getElem!_pos (lift f) i hi, lift, Vector.getElem_map, getElem!_pos f i hi]

theorem lift_rel (f : Poly) : Rel 1 (lift f) f := by
  intro i hi
  have he := lift_get f hi
  refine ⟨by rw [he, Nat.one_mul]; exact f[i]!.isLt, Fin.ext ?_⟩
  rw [Fin.val_ofNat, he]; exact Nat.mod_eq_of_lt f[i]!.isLt

/-- A layer of the forward butterflies on words. -/
def layerB (F : WPoly) (len : Nat) : WPoly := layF (wBlockN opB) F len (fun c => 128 / len + c) (128 / len)

/-- A layer of the inverse butterflies on words. -/
def layerIB (F : WPoly) (len : Nat) : WPoly :=
  layF (wBlockN opIB) F len (fun c => 256 / len - 1 - c) (128 / len)

theorem len_facts {len : Nat} (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128]) :
    0 < len ∧ 2 * len * (128 / len) = 256 ∧
      ∀ i < 256, (i % (2 * len) < len → i + len < 256) ∧ (¬ i % (2 * len) < len → len ≤ i) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
  rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨by decide, by decide, ?_⟩
  all_goals intro i hi; omega

theorem layerB_rel {b : Nat} (hb : b ≤ 13) {F : WPoly} {f : Poly} (hF : Rel b F f)
    {len : Nat} (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128]) :
    Rel (b + 2) (layerB F len) (nttLayer f len) := by
  have hl := len_facts hlen
  intro i hi
  rw [layerB, layF_get (wBlk_ok opB) F hl.1 _ (by omega) hi, nttLayer_get f hl.1 hl.2.1 hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    exact ⟨(opB_bound _ _ _ hb h0.1).1, by
      rw [(opB_residue _ _ _ (Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb))).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega)
    have h1 := hF i hi
    exact ⟨(opB_bound _ _ _ hb h0.1).2, by
      rw [(opB_residue _ _ _ (Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb))).2, h0.2, h1.2]⟩

theorem layerIB_rel {b : Nat} (hb : 1 ≤ b) (hb' : b ≤ 64) {F : WPoly} {f : Poly}
    (hF : Rel b F f) {len : Nat} (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128]) :
    Rel (2 * b) (layerIB F len) (nttInvLayer f len) := by
  have hl := len_facts hlen
  have lt : ∀ {x : Word}, x.val < b * q → x.val < 64 * q := fun h =>
    Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right q hb')
  intro i hi
  rw [layerIB, layF_get (wBlk_ok opIB) F hl.1 _ (by omega) hi, nttInvLayer_get f hl.1 hl.2.1 hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    exact ⟨(opIB_bound _ _ _ hb hb' h0.1 h1.1).1, by
      rw [(opIB_residue _ _ _ (lt h0.1) (lt h1.1)).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega)
    have h1 := hF i hi
    exact ⟨(opIB_bound _ _ _ hb hb' h0.1 h1.1).2, by
      rw [(opIB_residue _ _ _ (lt h0.1) (lt h1.1)).2, h0.2, h1.2]⟩

/-! ## Words in memory -/

/-- The words of `W` stored at `p`. -/
def LP (m : Mem) (p : Addr) (W : WPoly) : Prop := ∀ i < n, (coeffAt m p i).toNat = W[i]!.val

theorem lp_writeW {m : Mem} {p : Addr} {W : WPoly} (h : LP m p W) {j : Nat} (hj : j < n) (x : Word)
    {v : BitVec 32} (hv : v.toNat = x.val) : LP (m.writeW (coeffAddr p j) v) p (W.set! j x) := by
  intro i hi
  rw [coeffAt_writeW m p hi hj]
  split
  · subst j; rw [VG.Proof.MlKem.vget_set_self _ hi, hv]
  · rw [VG.Proof.MlKem.vget_set_ne _ hi ‹_›, h i hi]

theorem lp_lift {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) : LP m p (lift f) := fun i hi => by
  rw [polyIs_toNat h hi, lift_get f (by rw [n_eq] at hi; exact hi)]

theorem w64_load {v : BitVec 32} {x : Word} (h : v.toNat = x.val) : v.setWidth 64 = w64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem toW_store (v : BitVec 64) : (v.setWidth 32).toNat = (toW v).val := by
  rw [BitVec.toNat_setWidth, Fin.val_ofNat]

end VG.Proof.MlKem.RISCV64.Lazy
