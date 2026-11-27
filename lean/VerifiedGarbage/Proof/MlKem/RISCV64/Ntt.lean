module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Reduce
public import VerifiedGarbage.Proof.MlKem.NttLayer
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Reduce
meta import VerifiedGarbage.Proof.MlKem.NttLayer
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.MlKem.Blocks
public import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MlKem.Blocks
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Omega

/-! ### `MlKem.RISCV64.Lazy`, which this module and modules that import it used -/

section

/-!
# ML-KEM on RISC-V: the lazy butterflies' values

As ML-DSA's on RISC-V (`Proof/MlDsa/RISCV64/Arith/Ntt.lean`), for
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
  have e1 : R * Q < 2 ^ 64 * Q := Nat.mul_lt_mul_of_pos_right hr (by omega_using [hq])
  have e2 : 2988 * x < Q * 2 ^ 64 := Nat.mul_lt_mul_of_le_of_lt (by omega_using [hq]) hx (by omega_using [hq])
  have hle : T * Q ≤ x :=
    Nat.le_of_mul_le_mul_right (show T * Q * 2 ^ 64 ≤ x * 2 ^ 64 by omega_using [key]) (Nat.two_pow_pos 64)
  have h2 : x * 2 ^ 64 < T * Q * 2 ^ 64 + 2 * Q * 2 ^ 64 := by omega_using [hx, key, hq, e1]
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
    exact Nat.mod_eq_of_lt (by rw [q_eq] at hle; omega_using [])
  unfold barM
  generalize barQ x = B at hT ⊢
  generalize x.toNat * 5541226816974932 / 2 ^ 64 = T at hle hT ⊢
  subst hT
  rw [q_eq] at hle ⊢
  have hm : (B * 3329).toNat = B.toNat * 3329 := by
    rw [BitVec.toNat_mul, show (3329 : BitVec 64).toNat = 3329 from rfl]
    exact Nat.mod_eq_of_lt (by omega_using [hle])
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hm]; omega_using [hle]), hm]

theorem barM_lt (x : BitVec 64) : (barM x).toNat < 2 * q := by
  obtain ⟨hle, hlt⟩ := bar_spec x.toNat x.isLt
  rw [barM_toNat]; omega_using [hle, hlt]

theorem barM_mod (x : BitVec 64) : (barM x).toNat % q = x.toNat % q := by
  obtain ⟨hle, -⟩ := bar_spec x.toNat x.isLt
  rw [barM_toNat]
  generalize x.toNat * 5541226816974932 / 2 ^ 64 = T at hle ⊢
  have e : x.toNat = (x.toNat - T * q) + q * T := by rw [Nat.mul_comm q T]; omega_using [hle]
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
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])

/-! ## The forward butterfly -/

/-- The reduced product of `y` and the zeta. -/
def prod (y : Word) (z : Zq) : Nat := (barM (z64 z * w64 y)).toNat

theorem z64_mul (y : Word) (z : Zq) : (z64 z * w64 y).toNat = z.val * y.val := by
  have hz : z.val < 3329 := z.isLt
  have hy : y.val < 4294967296 := y.isLt
  have e1 : z.val % 2 ^ 64 = z.val := Nat.mod_eq_of_lt (by omega_using [hz])
  rw [BitVec.toNat_mul, w64_toNat, BitVec.toNat_ofNat, e1]
  have := Nat.mul_lt_mul_of_lt_of_le hz (Nat.le_of_lt hy) (by omega_using [])
  exact Nat.mod_eq_of_lt (by omega_using [this])

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
  · rw [BitVec.toNat_add, hx', Nat.mod_eq_of_lt (by omega_using [hx, ht]), Nat.mod_eq_of_lt (by omega_using [ht])]
  · have e : (w64 x - T + 6658).toNat = x.val + 6658 - T.toNat := by
      generalize w64 x = X at hx' ⊢
      bv_omega
    rw [e, Nat.mod_eq_of_lt (by omega_using [hx])]

theorem opB_bound (x y : Word) (z : Zq) {b : Nat} (hb : b ≤ 13) (hx : x.val < b * q) :
    (opB x y z).1.val < (b + 2) * q ∧ (opB x y z).2.val < (b + 2) * q := by
  have hv := opB_values x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb))
  have ht := prod_lt y z
  rw [hv.1, hv.2, Nat.add_mul]
  omega_using [hx, ht]

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
    omega_using [ht']

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
    have e1 : z.val % 2 ^ 64 = z.val := Nat.mod_eq_of_lt (by omega_using [hz])
    rw [BitVec.toNat_mul, hd, BitVec.toNat_ofNat, e1]
    have := Nat.mul_lt_mul_of_lt_of_le hz (show y.val + 213056 - x.val ≤ 2 ^ 19 by omega_using [hy]) (by omega_using [])
    exact Nat.mod_eq_of_lt (by omega_using [this])
  have hl := barM_lt (z64 z * (w64 y - w64 x + 213056))
  rw [q_eq] at hl
  refine ⟨?_, ?_, by rw [q_eq]; exact hl, ?_⟩
  · simp only [opIB, toW, Fin.val_ofNat]
    rw [BitVec.toNat_add, hx', hy', Nat.mod_eq_of_lt (by omega_using [hx, hy]), Nat.mod_eq_of_lt (by omega_using [])]
  · simp only [opIB, toW, Fin.val_ofNat, prodI]
    exact Nat.mod_eq_of_lt (by omega_using [hl])
  · have := barM_mod (z64 z * (w64 y - w64 x + 213056))
    rw [hp] at this
    exact this

theorem opIB_bound (x y : Word) (z : Zq) {b : Nat} (hb : 1 ≤ b) (hb' : b ≤ 64) (hx : x.val < b * q)
    (hy : y.val < b * q) : (opIB x y z).1.val < 2 * b * q ∧ (opIB x y z).2.val < 2 * b * q := by
  have hv := opIB_values x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb'))
    (Nat.lt_of_lt_of_le hy (Nat.mul_le_mul_right q hb'))
  rw [hv.1, hv.2.1, Nat.mul_assoc]
  constructor
  · omega_using [hx, hy]
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
      rw [q_eq] at hx hy ⊢; omega_using [hx]
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
  all_goals intro i hi; omega_using [hi]

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
    have h0 := hF (i - len) (by omega_using [hi])
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
    have h0 := hF (i - len) (by omega_using [hi])
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
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])]

theorem toW_store (v : BitVec 64) : (v.setWidth 32).toNat = (toW v).val := by
  rw [BitVec.toNat_setWidth, Fin.val_ofNat]

end VG.Proof.MlKem.RISCV64.Lazy

end

end

/-!
# ML-KEM on RISC-V: `vg_mlkem_ntt`

As on PPC64LE (`Proof/MlKem/PPC64LE/Ntt.lean`), with no registers to save:
the table of the zetas stored (`setup_ok`); then the three nested loops of
`layerB`, `layF` and `wBlockN` on words (`Lazy.lean`, `Proof/MlKem/Blocks.lean`),
with an invariant each (`LInv`, `BInv`, `FInv`) saying which words `f` holds
(`LP`); the lazy butterfly is symbolically executed once for any (aligned)
pointers (`bfly_ok`), and stores the words `opB` gives (`lp_bfly`). Layer `ℓ`
has `len = 128 / 2^ℓ` and `2^ℓ` blocks. The seven layers leave words less
than `15 q` congruent to `NTT f` (`nttLB_rel`), which the last loop reduces,
coefficient by coefficient (`CInv`, `cstep`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Ntt

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Proof.MlKem.RISCV64.Lazy (Word WPoly LP lp_writeW lp_lift w64 w64_load toW toW_store z64 opB layerB Rel
  lift residue layerB_rel barM redM redM_toNat barQ)
open VG.Proof.MlKem (wbfly wBlockN wbfly_get layF)

/-- The forward butterflies of a block, on words. -/
abbrev fblk : WPoly → Nat → Nat → Nat → Nat → WPoly := wBlockN opB

/-! ## Values -/

/-- A butterfly writes `f[j + len]`, then `f[j]`. -/
theorem lp_bfly {m : Mem} {F : Addr} {W : WPoly} (h : LP m F W) {j len : Nat}
    (hj : j + len < n) (z : Zq) {v₁ v₂ : BitVec 32} (h₁ : v₁.toNat = (opB W[j]! W[j + len]! z).2.val)
    (h₂ : v₂.toNat = (opB W[j]! W[j + len]! z).1.val) :
    LP ((m.writeW (coeffAddr F (j + len)) v₁).writeW (coeffAddr F j) v₂) F (wbfly opB W j len z) :=
  lp_writeW (lp_writeW h hj _ h₁) (by omega_arith) _ h₂

/-! ## The butterfly -/

section
variable {s : State} {x y z c : BitVec 64}

theorem bfly_ok (h5 : s.gpr .a2 = x) (h6 : s.gpr .a3 = y) (h7 : s.gpr .a4 = z)
    (h8 : s.gpr .a5 = 5541226816974932) (h9 : s.gpr .a6 = 3329) (h11 : s.gpr .t1 = c) (h12 : s.gpr .t5 = 6658)
    (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) y 4)
    (oa : InRegions s.wr x 4) (ob : InRegions s.wr y 4) (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0) :
    WP isa (.block bflyBody) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .a3 = y + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a0 = s.gpr .a0 ∧
      s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a4 = z ∧ s'.gpr .a5 = 5541226816974932 ∧ s'.gpr .a6 = 3329 ∧
      s'.gpr .a7 = s.gpr .a7 ∧ s'.gpr .t5 = 6658 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW y (((s.mem.readW x 32).setWidth 64 -
            barM (z * (s.mem.readW y 32).setWidth 64) + 6658).setWidth 32)).writeW x
          (((s.mem.readW x 32).setWidth 64 + barM (z * (s.mem.readW y 32).setWidth 64)).setWidth 32) := by
  crun [bflyBody, barrettM, barM, barQ, kept, h5, h6, h7, h8, h9, h11, h12, ia, ib, oa, ob, ax, ay,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## Loops -/

section
variable (s₀ : State)

abbrev F : Addr := s₀.gpr .a0
abbrev S : Addr := s₀.gpr .a1
abbrev P : Poly := polyAt s₀.mem (F s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (F s₀), polyRegion (S s₀)]
  disj : (polyRegion (F s₀)).Disjoint (polyRegion (S s₀))
  fitF : (F s₀).toNat + 1024 ≤ 2 ^ 64
  fitS : (S s₀).toNat + 1024 ≤ 2 ^ 64
  red : Reduced s₀.mem (F s₀)
  alF : (F s₀).toNat % 4 = 0
  alS : (S s₀).toNat % 8 = 0

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  tab : ∀ j < 128, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (zetaTable.getD j 0)
  poly : PolyIs m₁ (F s₀) (P s₀)

/-- What every loop keeps, with the constant `k5` in `t5`. -/
structure Env (k5 : BitVec 64) (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  a0 : s.gpr .a0 = F s₀ + BitVec.ofNat 64 1024
  a5 : s.gpr .a5 = 5541226816974932
  a6 : s.gpr .a6 = 3329
  t5 : s.gpr .t5 = k5
  kept : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (F s₀)] m₁ s.mem

theorem Env.inW {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} {k5 : BitVec 64} (h : Env k5 s₀ m₁ s) {a : Addr} {k : Nat}
    (hc : (polyRegion (F s₀)).Contains a k) : InRegions s.wr a k := by
  rw [h.wr, hp.wr]; exact ⟨_, by simp, hc⟩

theorem Env.inR {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} {k5 : BitVec 64} (h : Env k5 s₀ m₁ s) {a : Addr} {k : Nat}
    (hc : (polyRegion (F s₀)).Contains a k) : InRegions (s.rd ++ s.wr) a k := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, hc⟩

theorem Env.inRS {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {s : State} {k5 : BitVec 64} (h : Env k5 s₀ m₁ s) {a : Addr} {k : Nat}
    (hc : (polyRegion (S s₀)).Contains a k) : InRegions (s.rd ++ s.wr) a k := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, hc⟩

/-- After `t` butterflies of the block from `st` with the zeta `zeta k` of
the layer with `len`, from `Q`: the zeta pointer is at `k + 1`. -/
structure FInv (s₀ : State) (m₁ : Mem) (Q : WPoly) (len k st : Nat) (t : Nat) (s : State) : Prop where
  env : Env 6658 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (k + 1))
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (st + t))
  a3 : s.gpr .a3 = F s₀ + BitVec.ofNat 64 (4 * (st + len + t))
  a4 : s.gpr .a4 = BitVec.ofNat 64 (zeta k).val
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * len)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (len - t)
  poly : LP s.mem (F s₀) (fblk Q len k st t)

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {Q : WPoly} {len k st t : Nat}
    (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : FInv s₀ m₁ Q len k st t s) :
    WP isa (.block bflyBody) s fun s' =>
      FInv s₀ m₁ Q len k st (t + 1) s' ∧ (s'.gpr .t1 != 0) = decide (t + 1 ≠ len) := by
  have ea : F s₀ + BitVec.ofNat 64 (4 * (st + t)) = coeffAddr (F s₀) (st + t) := rfl
  have eb : F s₀ + BitVec.ofNat 64 (4 * (st + len + t)) = coeffAddr (F s₀) (st + t + len) := by
    rw [show st + len + t = st + t + len by omega_arith]
  have ca := coeff_contains (F s₀) (i := st + t) (by rw [n_eq]; omega_arith)
  have cb := coeff_contains (F s₀) (i := st + t + len) (by rw [n_eq]; omega_arith)
  have va := h.poly (st + t) (by rw [n_eq]; omega_arith)
  have vb := h.poly (st + t + len) (by rw [n_eq]; omega_arith)
  refine WP.mono (bfly_ok h.a2 h.a3 h.a4 h.env.a5 h.env.a6 h.t1 h.env.t5
    (by rw [ea]; exact h.env.inR hp ca) (by rw [eb]; exact h.env.inR hp cb)
    (by rw [ea]; exact h.env.inW hp ca) (by rw [eb]; exact h.env.inW hp cb)
    (align4_add hp.alF _) (align4_add hp.alF _))
    fun s' ⟨r5, r6, r11, r3, r4, r7, r8, r9, r10, r12, kp, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.a0, r8, r9, r12, fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
        wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, r4.trans h.a1, ?_, ?_, r7, r10.trans h.a7, ?_, ?_⟩, ?_⟩
  · rw [m, ea, eb]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ cb).writeW (List.mem_singleton_self _) _ ca
  · rw [r5, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r6, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub ht
  · rw [m, ea, eb, ← coeffAt_eq, ← coeffAt_eq, w64_load va, w64_load vb,
      show fblk Q len k st (t + 1) = wbfly opB (fblk Q len k st t) (st + t) len (zeta k)
        from foldl_range'_succ _ _ _ _]
    exact lp_bfly h.poly (by rw [n_eq]; omega_arith) _ (toW_store _) (toW_store _)
  · rw [r11, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub ht]
    exact count_nz ht (by omega_arith)

/-! ## Blocks -/

section
variable {s : State} {x4 x5 x10 y : BitVec 64}

/-- The start of a block: its zeta, the pointer to the second half, the count. -/
theorem bpre_ok (h4 : s.gpr .a1 = x4) (h5 : s.gpr .a2 = x5) (h10 : s.gpr .a7 = x10)
    (i4 : InRegions (s.rd ++ s.wr) x4 4) (a4 : x4.toNat % 4 = 0) :
    WP isa (.block [.load .w .a4 .a1 0, .addi .a1 .a1 4, .add .a3 .a2 .a7, .shift .srl .d .t1 .a7 2]) s
      fun s' => s'.gpr .a4 = (s.mem.readW x4 32).setWidth 64 ∧ s'.gpr .a1 = x4 + 4 ∧
        s'.gpr .a3 = x5 + x10 ∧ s'.gpr .t1 = x10 >>> 2 ∧ s'.gpr .a2 = x5 ∧ s'.gpr .a7 = x10 ∧
        s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h4, h5, h10, i4, a4, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  simp [Mem.readW, Mem.read]

/-- The end of a block: the next block's start, compared with the end. -/
theorem bpost_ok (h6 : s.gpr .a3 = y) :
    WP isa (.block [.addi .a2 .a3 0, .sub .t0 .a2 .a0]) s fun s' =>
      s'.gpr .a2 = y ∧ s'.gpr .t0 = y - s.gpr .a0 ∧ s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a1 = s.gpr .a1 ∧
        s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .a7 = s.gpr .a7 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h6, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

end

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : WPoly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : Env 6658 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (nb + c))
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (2 * len * c))
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * len)
  poly : LP s.mem (F s₀) (layF fblk Q len (fun c => 128 / len + c) c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {Q : WPoly} {len nb c : Nat}
    (hl2 : 2 ≤ len) (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : BInv s₀ m₁ Q len nb c s) :
    WP isa nttBlockCode s fun s' => BInv s₀ m₁ Q len nb (c + 1) s' ∧ (s'.gpr .t0 != 0) = decide (c + 1 ≠ nb) := by
  have hl : 0 < len := by omega_arith
  have hdiv : 128 / len = nb := by rw [← hnb, Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  have hk : nb + c < 128 := by
    have : 2 * nb ≤ len * nb := Nat.mul_le_mul_right nb hl2
    omega_arith
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * (nb + c))) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have vz : (s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * (nb + c))) 32).setWidth 64 =
      BitVec.ofNat 64 (zeta (128 / len + c)).val := by
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), hm.tab _ hk, zetaTable_eq, zetas_getD hk, hdiv,
      setWidth64_ofNat (by have := val_lt (zeta (nb + c)); omega_arith)]
  refine WP.seq (WP.mono (bpre_ok h.a1 h.a2 h.a7 (h.env.inRS hp cS)
    (align4_add (by have := hp.alS; omega_using [this]) _))
    fun s₁ ⟨r7, r4, r6, r11, r5, r10, r3, r8, r9, r12, kp, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : FInv s₀ m₁ (layF fblk Q len (fun c => 128 / len + c) c) len (128 / len + c) (2 * len * c) 0 s₁ := by
    refine ⟨⟨r3.trans h.env.a0, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5,
      fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, ?_, ?_, ?_, r10, ?_,
      m ▸ h.poly⟩
    · rw [r4, hdiv]
      exact (ptr_add _ _ 4).trans (by rw [show 4 * (nb + c) + 4 = 4 * (nb + c + 1) by omega_arith])
    · rw [r5, Nat.add_zero]
    · rw [r6, ptr_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len + 0) by omega_arith]
    · rw [r7, vz]
    · rw [r11, lsr2 (by omega_arith)]
  refine wp_loop_nz (FInv s₀ m₁ (layF fblk Q len (fun c => 128 / len + c) c) len (128 / len + c) (2 * len * c)) hl
    (fun t ht s h => fstep hp (by omega_arith) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (bpost_ok h₂.a3) fun s' ⟨r5, r0, r3, r4, r8, r9, r10, r12, kp, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.a0, r8.trans h₂.env.a5, r9.trans h₂.env.a6, r12.trans h₂.env.t5,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, r10.trans h₂.a7, ?_⟩, ?_⟩
  · rw [r4, h₂.a1, hdiv, Nat.add_assoc]
  · rw [r5]; congr 2; rw [Nat.mul_succ]; omega_arith
  · rw [m, layF, foldl_range_succ, ← layF]; exact h₂.poly
  · rw [r0, h₂.env.a0, ptr_ne _ (by omega_arith) (by omega_arith)]
    refine decide_eq_decide.mpr ⟨fun e e' => e ?_, fun e e' => e ?_⟩
    · subst e'; rw [Nat.mul_add, Nat.mul_one] at *; omega_arith
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega_arith
      exact Nat.eq_of_mul_eq_mul_left hl this

/-! ## Layers -/

/-- What the layers' loop counters are: layer `ℓ` has `len = 128 >>> ℓ` and
`2^ℓ` blocks. -/
theorem layer_facts : ∀ ℓ < 7, 2 ≤ 128 >>> ℓ ∧ (128 >>> ℓ) * 2 ^ ℓ = 128 ∧ 0 < 2 ^ ℓ ∧
    2 ^ ℓ + 2 ^ ℓ = 2 ^ (ℓ + 1) ∧ 128 / (128 >>> ℓ) = 2 ^ ℓ ∧
    BitVec.ofNat 64 (4 * (128 >>> ℓ)) >>> 1 = BitVec.ofNat 64 (4 * (128 >>> (ℓ + 1))) ∧
    (BitVec.ofNat 64 (4 * (128 >>> (ℓ + 1))) - 4 != 0) = decide (ℓ + 1 ≠ 7) := by
  decide

section
variable {s : State} {x3 x10 : BitVec 64}

theorem lpre_ok (h3 : s.gpr .a0 = x3) :
    WP isa (.block [.addi .a2 .a0 (-1024)]) s fun s' =>
      s'.gpr .a2 = x3 - 1024 ∧ s'.gpr .a0 = x3 ∧ s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a5 = s.gpr .a5 ∧
        s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .a7 = s.gpr .a7 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h3, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

theorem lpost_ok (h10 : s.gpr .a7 = x10) :
    WP isa (.block [.shift .srl .d .a7 .a7 1, .addi .t0 .a7 (-4)]) s fun s' =>
      s'.gpr .a7 = x10 >>> 1 ∧ s'.gpr .t0 = x10 >>> 1 - 4 ∧ s'.gpr .a0 = s.gpr .a0 ∧
        s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h10, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

end

/-- The first `ℓ` layers of the butterflies on words. -/
def nttLB (ℓ : Nat) (W : WPoly) : WPoly := (nttLens.take ℓ).foldl layerB W

theorem nttLB_succ (W : WPoly) {ℓ : Nat} (hℓ : ℓ < 7) : nttLB (ℓ + 1) W = layerB (nttLB ℓ W) (128 >>> ℓ) := by
  have e : nttLens[ℓ]'(by simp [nttLens]; omega_arith) = 128 >>> ℓ := by
    revert ℓ; decide
  unfold nttLB
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simp [nttLens]; omega_arith), e]
  rfl

theorem len_mem : ∀ ℓ < 7, 128 >>> ℓ ∈ [2, 4, 8, 16, 32, 64, 128] := by decide

/-- After `ℓ` layers, words less than `(2ℓ + 1) q` congruent to the
specification's. -/
theorem nttLB_rel (f : Poly) : ∀ ℓ ≤ 7, Rel (2 * ℓ + 1) (nttLB ℓ (lift f)) (nttL ℓ f)
  | 0, _ => Lazy.lift_rel f
  | ℓ + 1, h => by
    rw [nttLB_succ _ (by omega_arith), nttL_succ _ (by omega_arith)]
    exact layerB_rel (by omega_arith) (nttLB_rel f ℓ (by omega_arith)) (len_mem ℓ (by omega_arith))

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : Env 6658 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * 2 ^ ℓ)
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * (128 >>> ℓ))
  poly : LP s.mem (F s₀) (nttLB ℓ (lift (P s₀)))

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 7) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa nttLayerCode s fun s' => LInv s₀ m₁ (ℓ + 1) s' ∧ (s'.gpr .t0 != 0) = decide (ℓ + 1 ≠ 7) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := layer_facts ℓ hℓ
  refine WP.seq (WP.mono (lpre_ok h.env.a0)
    fun s₁ ⟨r5, r3, r4, r8, r9, r10, r12, kp, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : BInv s₀ m₁ (nttLB ℓ (lift (P s₀))) (128 >>> ℓ) (2 ^ ℓ) 0 s₁ := by
    refine ⟨⟨r3, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5, fun r hr => (kp r hr).trans (h.env.kept r hr),
      rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩,
      by rw [r4, h.a1, Nat.add_zero], ?_, r10.trans h.a7, ?_⟩
    · rw [r5, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_nz (BInv s₀ m₁ (nttLB ℓ (lift (P s₀))) (128 >>> ℓ) (2 ^ ℓ)) f3
    (fun c hc s h => bstep hp hm f1 f2 hc h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (lpost_ok h₂.a7) fun s' ⟨r10, r0, r3, r4, r8, r9, r12, kp, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.a0, r8.trans h₂.env.a5, r9.trans h₂.env.a6, r12.trans h₂.env.t5,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r4, h₂.a1, f4]
  · rw [r10, f6]
  · rw [m, nttLB_succ _ hℓ, layerB]
    exact (congrArg (fun b => LP s₂.mem (F s₀) (layF fblk (nttLB ℓ (lift (P s₀))) (128 >>> ℓ)
      (fun c => 128 / (128 >>> ℓ) + c) b)) f5).mpr h₂.poly
  · rw [r0, f6, f7]

/-! ## Setup and the end -/

theorem sub_low (p : Addr) {k L : Nat} (h : k ≤ L) : Region.Sub ⟨p, k⟩ ⟨p, L⟩ := fun a ha => by
  simp only [Region.Contains] at ha ⊢; omega_arith

/-- The table stored in `scratch`. -/
theorem setup_base {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table zetaTable .a1)) s₀ fun s =>
      Setup s₀ s.mem ∧ (∀ r, r ≠ .t0 → r ≠ .t2 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
        s.sp = s₀.sp := by
  have fS := hp.fitS
  have wS : ∀ {o k : Nat}, o + k ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) k := fun h => by
    rw [hp.wr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_arith)⟩
  have a8 : (s₀.gpr .a1).toNat % 8 = 0 := hp.alS
  refine WP.mono (table_ok zetaTable (by decide) (b := .a1) (by decide) (by decide) rfl
    (by omega_using [a8]) fun k hk => wS (by omega_arith)) fun s₂ h₂ => ?_
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    refine h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    rw [List.mem_singleton] at hr; subst hr
    exact sub_low _ (by omega_arith)
  exact ⟨⟨fun j hj => h₂.tab j hj, polyIs_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj) ⟨hp.red, rfl⟩⟩,
    h₂.gpr, h₂.rd, h₂.wr, h₂.sp⟩

theorem tail_ok {s : State} :
    WP isa (.block (constsM ++ ([.add .t5 .a6 .a6, .addi .a0 .a0 1024, .addi .a1 .a1 4, .li .a7 512] : List Instr))) s
      fun s' => s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 1024 ∧ s'.gpr .a1 = s.gpr .a1 + 4 ∧
        s'.gpr .a5 = 5541226816974932 ∧ s'.gpr .a6 = 3329 ∧ s'.gpr .t5 = 6658 ∧ s'.gpr .a7 = 512 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [constsM, loadM, liq, Nat.reduceLT, ite_false, List.cons_append, List.nil_append,
    Int.reduceSub, Int.reduceNeg, Int.cast_ofNat_Int]
  crun [kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table zetaTable .a1 ++ constsM ++
      ([.add .t5 .a6 .a6, .addi .a0 .a0 1024, .addi .a1 .a1 4, .li .a7 512] : List Instr))) s₀
      fun s => Setup s₀ s.mem ∧ LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  refine WP.mono tail_ok fun s ⟨r3, r4, r8, r9, r12, r10, kp, m, rd', wr', sp'⟩ => ?_
  rw [m]
  refine ⟨hm, ⟨⟨by rw [r3, e .a0 (by decide) (by decide)], r8, r9, r12, fun r hr => ?_, rd'.trans rd,
    wr'.trans wr, sp'.trans sp, by rw [m]; exact Frame.refl _ _⟩,
    by rw [r4, e .a1 (by decide) (by decide)]; rfl, r10, m ▸ lp_lift hm.poly⟩⟩
  rw [kp r hr, e r (by revert r hr; decide) (by revert r hr; decide)]

/-! ## The reduction -/

/-- The first `i` words of `W` reduced modulo `q`. -/
def canonN (W : WPoly) (i : Nat) : WPoly :=
  (List.range i).foldl (fun w j => w.set! j (Fin.ofNat _ (w[j]!.val % q))) W

theorem canonN_zero (W : WPoly) : canonN W 0 = W := rfl

theorem canonN_succ (W : WPoly) (i : Nat) :
    canonN W (i + 1) = (canonN W i).set! i (Fin.ofNat _ ((canonN W i)[i]!.val % q)) :=
  foldl_range_succ _ _ _

theorem canonN_get (W : WPoly) : ∀ i ≤ n, ∀ j < n,
    (canonN W i)[j]! = if j < i then Fin.ofNat _ (W[j]!.val % q) else W[j]!
  | 0, _, j, _ => by rw [ite_eq_right (Nat.not_lt_zero j)]; rfl
  | i + 1, hi, j, hj => by
    have ih := canonN_get W i (by omega_arith)
    rw [canonN_succ]
    by_cases e : i = j
    · subst e
      rw [VG.Proof.MlKem.vget_set_self _ hj, ih i hj, ite_eq_right (Nat.lt_irrefl i),
        ite_eq_left (Nat.lt_succ_self i)]
    · rw [VG.Proof.MlKem.vget_set_ne _ hj e, ih j hj]
      by_cases hji : j < i
      · rw [ite_eq_left hji, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hji, ite_eq_right (by omega_arith)]

/-- A word reduced modulo `q`, as `reduceM` stores it. -/
theorem red_store (x : Word) :
    ((redM (w64 x)).setWidth 32).toNat = (Fin.ofNat 4294967296 (x.val % q) : Word).val := by
  have hq : x.val % q < 2 ^ 32 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [BitVec.toNat_setWidth, redM_toNat, Lazy.w64_toNat, Fin.val_ofNat, Nat.mod_eq_of_lt hq]

/-- After `i` words of `W` reduced. -/
structure CInv (s₀ : State) (m₁ : Mem) (W : WPoly) (i : Nat) (s : State) : Prop where
  env : Env 6658 s₀ m₁ s
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * i)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (256 - i)
  poly : LP s.mem (F s₀) (canonN W i)

section
variable {s : State} {x c : BitVec 64}

theorem canon_ok (h5 : s.gpr .a2 = x) (h8 : s.gpr .a5 = 5541226816974932)
    (h9 : s.gpr .a6 = 3329) (h11 : s.gpr .t1 = c)
    (ia : InRegions (s.rd ++ s.wr) x 4) (oa : InRegions s.wr x 4) (ax : x.toNat % 4 = 0) :
    WP isa (.block canonBody) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a0 = s.gpr .a0 ∧
      s'.gpr .a5 = 5541226816974932 ∧ s'.gpr .a6 = 3329 ∧ s'.gpr .t5 = s.gpr .t5 ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW x ((redM ((s.mem.readW x 32).setWidth 64)).setWidth 32) := by
  crun [canonBody, reduceM, barrettM, fixup, redM, barM, barQ, fixq, kept, h5, h8, h9, h11, ia, oa, ax,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

theorem cstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {W : WPoly} {i : Nat} (hi : i < 256) {s : State}
    (h : CInv s₀ m₁ W i s) :
    WP isa (.block canonBody) s fun s' => CInv s₀ m₁ W (i + 1) s' ∧ (s'.gpr .t1 != 0) = decide (i + 1 ≠ 256) := by
  have ca := coeff_contains (F s₀) (i := i) (by rw [n_eq]; omega_arith)
  have va := h.poly i (by rw [n_eq]; omega_arith)
  refine WP.mono (canon_ok h.a2 h.env.a5 h.env.a6 h.t1 (h.env.inR hp ca) (h.env.inW hp ca)
    (align4_add hp.alF _))
    fun s' ⟨r5, r11, r3, r8, r9, r12, kp, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.a0, r8, r9, r12.trans h.env.t5, fun r hr => (kp r hr).trans (h.env.kept r hr),
        rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [m]; exact h.env.frame.writeW (List.mem_singleton_self _) _ ca
  · rw [r5]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub hi
  · rw [m, show F s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (F s₀) i from rfl, ← coeffAt_eq, w64_load va,
      canonN_succ]
    exact lp_writeW h.poly (by rw [n_eq]; omega_arith) _ (red_store _)
  · rw [r11, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by omega_arith)

/-- Words less than `15 q`, each reduced: the polynomial they are congruent to. -/
theorem canon_full {m : Mem} {p : Addr} {W : WPoly} {f : Poly} (hr : Rel 15 W f) (h : LP m p (canonN W 256)) :
    PolyIs m p f := polyIs_of_toNat fun i hi => by
  have hi' : i < 256 := by rw [n_eq] at hi; exact hi
  rw [h i hi, canonN_get W 256 (by rw [n_eq]) i hi, ite_eq_left hi', ← (hr i hi').2, Fin.val_ofNat, Fin.val_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < q)) (by decide : q ≤ 4294967296))]

theorem cpre_ok {s : State} :
    WP isa (.block [.addi .a2 .a0 (-1024), .li .t1 256]) s
      fun s' => s'.gpr .a2 = s.gpr .a0 - 1024 ∧ s'.gpr .t1 = BitVec.ofNat 64 256 ∧ s'.gpr .a0 = s.gpr .a0 ∧
        s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ntt s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .ra = s₀.gpr .ra ∧ PolyIs s.mem (F s₀) (Spec.MlKem.ntt (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => ?_)
  refine WP.seq (wp_loop_nz (LInv s₀ s₁.mem) (N := 7) (by decide) (fun ℓ hℓ s h => lstep hp hm hℓ h)
    (fun s h => ?_) h₁)
  refine WP.seq (WP.mono cpre_ok fun s₂ ⟨r5, r11, r3, r8, r9, r12, kp, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_nz (CInv s₀ s₁.mem (nttLB 7 (lift (P s₀)))) (N := 256) (by decide)
    (fun i hi s h => cstep hp hi h) (fun s' h' => ⟨fun r hr => h'.env.kept r (preserved_sub r hr), h'.env.sp,
      h'.env.kept .ra (by decide), by
        rw [ntt_eq_nttL]; exact canon_full (nttLB_rel (P s₀) 7 (by decide)) h'.poly⟩) ?_
  refine ⟨⟨r3.trans h.env.a0, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5,
    fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
    wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, r11, ?_⟩
  · rw [r5, h.env.a0, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
  · rw [m, canonN_zero]; exact h.poly

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

end VG.Proof.MlKem.RISCV64.Ntt
