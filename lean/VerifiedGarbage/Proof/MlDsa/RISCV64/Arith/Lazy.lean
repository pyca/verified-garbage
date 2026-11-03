module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
public import VerifiedGarbage.Proof.MlDsa.Arith.Lazy
public import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA on RISC-V: the lazy butterflies' values

The butterflies of `Impl/MlDsa/RISCV64/Arith.lean` reduce only the product,
to `barv` of it, in `[0, 2q)` (`Common.lean`), and store the sum and the
difference as they are: the coefficients between layers are words
(`Proof/MlDsa/Arith/Lazy.lean`'s `Word`) congruent to the specification's,
and bounded by a multiple of `q` that grows with each layer, as on x86-64
(`Proof/MlDsa/X86_64/Arith/LazyInvariant.lean`).

* `opB` is what the forward butterfly stores, `(x + t, x − t + 2q)` for the
  reduced product `t` of `y` and the zeta, computed on 64 bits and stored as
  the low word, so that the stores are `opB` for every input
  (`Ntt.lean`); for `x < 15q` it is that sum and difference
  (`opB_values`), less than `2q` more than `x` and congruent to the
  specification's butterfly (`opB_bound`, `opB_residue`). A layer then
  takes `Rel b` to `Rel (b + 2)` (`layerB_rel`): eight layers from `Rel 1`
  end at `Rel 17`.
* `opIB` is the inverse butterfly's, `(x + y, t)` for the reduced product
  `t` of the zeta and `x − y + 128q`: for `x, y < b q` with `b ≤ 128`, that
  sum and a product in `[0, 2q)` (`opIB_values`), so a layer takes `Rel b` to
  `Rel 2b` (`layerIB_rel`), and eight layers from `Rel 1` end at `Rel 256`,
  every coefficient less than `256 q < 2³¹`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Arith.Lazy

open VG
open VG.Spec.MlDsa (q n Zq zetas)
open VG.Proof.MlDsa.Arith (q_eq n_eq val_lt)
open VG.Proof.MlDsa.Arith.Lazy (Word Poly bfly blockN layF block_ok)
open VG.Proof.MlDsa.RISCV64.Arith (barv barv_lt barv_mod)

/-- A word on 64 bits. -/
abbrev w64 (x : Word) : BitVec 64 := BitVec.ofNat 64 x.val

/-- The low word of a value on 64 bits. -/
abbrev toW (v : BitVec 64) : Word := Fin.ofNat _ v.toNat

/-- A zeta on 64 bits. -/
abbrev z64 (z : Zq) : BitVec 64 := BitVec.ofNat 64 z.val

/-- The residue of a word. -/
abbrev residue (x : Word) : Zq := Fin.ofNat q x.val

/-! ## The forward butterfly -/

/-- The reduced product of `y` and the zeta. -/
def prod (y : Word) (z : Zq) : Nat := (barv (z64 z * w64 y)).toNat

theorem z64_mul (y : Word) (z : Zq) : (z64 z * w64 y).toNat = z.val * y.val := by
  have hz : z.val < 8380417 := z.isLt
  have hy : y.val < 4294967296 := y.isLt
  have e1 : z.val % 2 ^ 64 = z.val := Nat.mod_eq_of_lt (by omega)
  have e2 : y.val % 2 ^ 64 = y.val := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, e1, e2]
  have := Nat.mul_lt_mul_of_lt_of_le hz (Nat.le_of_lt hy) (by omega)
  exact Nat.mod_eq_of_lt (by omega)

theorem prod_lt (y : Word) (z : Zq) : prod y z < 2 * q := barv_lt _

theorem prod_mod (y : Word) (z : Zq) : prod y z % q = z.val * y.val % q := by
  rw [prod, barv_mod, z64_mul]

/-- What the forward butterfly stores: `x + t` and `x − t + 2q`, on 64 bits,
as words. -/
def opB (x y : Word) (z : Zq) : Word × Word :=
  (toW (w64 x + barv (z64 z * w64 y)), toW (w64 x - barv (z64 z * w64 y) + 16760834))

theorem opB_values (x y : Word) (z : Zq) (hx : x.val < 15 * q) :
    (opB x y z).1.val = x.val + prod y z ∧ (opB x y z).2.val = x.val + 2 * q - prod y z := by
  have ht := prod_lt y z
  have hx' : (w64 x).toNat = x.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)
  simp only [opB, toW, Fin.val_ofNat]
  unfold prod at ht ⊢
  generalize barv (z64 z * w64 y) = T at ht ⊢
  rw [q_eq] at hx ht ⊢
  constructor
  · rw [BitVec.toNat_add, hx', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · have e : (w64 x - T + 16760834).toNat = x.val + 16760834 - T.toNat := by
      generalize w64 x = X at hx' ⊢
      bv_omega
    rw [e, Nat.mod_eq_of_lt (by omega)]

theorem opB_bound (x y : Word) (z : Zq) {b : Nat} (hb : b ≤ 15) (hx : x.val < b * q) :
    (opB x y z).1.val < (b + 2) * q ∧ (opB x y z).2.val < (b + 2) * q := by
  have hv := opB_values x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb))
  have ht := prod_lt y z
  rw [hv.1, hv.2, Nat.add_mul]
  omega

theorem opB_residue (x y : Word) (z : Zq) (hx : x.val < 15 * q) :
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
    have ht' : prod y z < 2 * 8380417 := ht
    change (x.val + 2 * 8380417 - prod y z) % 8380417 =
      (8380417 - prod y z % 8380417 + x.val % 8380417) % 8380417
    omega

/-! ## The inverse butterfly -/

/-- The reduced product of the zeta and `x − y + 128 q`, on 64 bits. -/
def prodI (x y : Word) (z : Zq) : Nat := (barv (z64 z * (w64 x - w64 y + 1072693376))).toNat

/-- What the inverse butterfly stores: `x + y`, and the reduced product of
the zeta and `x − y + 128 q`, as words. -/
def opIB (x y : Word) (z : Zq) : Word × Word :=
  (toW (w64 x + w64 y), toW (barv (z64 z * (w64 x - w64 y + 1072693376))))

theorem opIB_values (x y : Word) (z : Zq) (hx : x.val < 128 * q) (hy : y.val < 128 * q) :
    (opIB x y z).1.val = x.val + y.val ∧ (opIB x y z).2.val = prodI x y z ∧
      prodI x y z < 2 * q ∧ prodI x y z % q = z.val * (x.val + 128 * q - y.val) % q := by
  have hx' : (w64 x).toNat = x.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)
  have hy' : (w64 y).toNat = y.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := y.isLt; omega)
  have hz : z.val < 8380417 := z.isLt
  have hx2 : x.val < 128 * 8380417 := hx
  have hy2 : y.val < 128 * 8380417 := hy
  have hd : (w64 x - w64 y + 1072693376).toNat = x.val + 1072693376 - y.val := by
    generalize w64 x = X at hx' ⊢
    generalize w64 y = Y at hy' ⊢
    bv_omega
  have hp : (z64 z * (w64 x - w64 y + 1072693376)).toNat = z.val * (x.val + 1072693376 - y.val) := by
    have e1 : z.val % 2 ^ 64 = z.val := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_mul, hd, BitVec.toNat_ofNat, e1]
    have := Nat.mul_lt_mul_of_lt_of_le hz (show x.val + 1072693376 - y.val ≤ 2 ^ 31 by omega) (by omega)
    exact Nat.mod_eq_of_lt (by omega)
  have hl := barv_lt (z64 z * (w64 x - w64 y + 1072693376))
  have hl2 : (barv (z64 z * (w64 x - w64 y + 1072693376))).toNat < 2 * 8380417 := hl
  refine ⟨?_, ?_, hl, ?_⟩
  · simp only [opIB, toW, Fin.val_ofNat]
    rw [BitVec.toNat_add, hx', hy', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · simp only [opIB, toW, Fin.val_ofNat, prodI]
    exact Nat.mod_eq_of_lt (by omega)
  · have := barv_mod (z64 z * (w64 x - w64 y + 1072693376))
    rw [hp] at this
    exact this

theorem opIB_bound (x y : Word) (z : Zq) {b : Nat} (hb : 1 ≤ b) (hb' : b ≤ 128) (hx : x.val < b * q)
    (hy : y.val < b * q) : (opIB x y z).1.val < 2 * b * q ∧ (opIB x y z).2.val < 2 * b * q := by
  have hv := opIB_values x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb'))
    (Nat.lt_of_lt_of_le hy (Nat.mul_le_mul_right q hb'))
  rw [hv.1, hv.2.1, Nat.mul_assoc]
  constructor
  · omega
  · exact Nat.lt_of_lt_of_le hv.2.2.1 (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left q hb))

theorem opIB_residue (x y : Word) (z : Zq) (hx : x.val < 128 * q) (hy : y.val < 128 * q) :
    residue (opIB x y z).1 = residue x + residue y ∧
    residue (opIB x y z).2 = z * (residue x - residue y) := by
  have hv := opIB_values x y z hx hy
  constructor
  · apply Fin.ext
    rw [Fin.val_add]
    change (opIB x y z).1.val % q = (x.val % q + y.val % q) % q
    rw [hv.1, Nat.add_mod]
  · apply Fin.ext
    change (opIB x y z).2.val % q = (z * (residue x - residue y)).val
    rw [hv.2.1, hv.2.2.2, Fin.val_mul, Fin.val_sub, residue, residue, Fin.val_ofNat, Fin.val_ofNat]
    have hl : (x.val + 128 * q - y.val) % q = (q - y.val % q + x.val % q) % q := by
      rw [q_eq] at hx hy ⊢; omega
    rw [Nat.mul_mod, hl, Nat.mul_mod z.val ((q - y.val % q + x.val % q) % q), Nat.mod_mod]

/-! ## Layers -/

/-- Words bounded by `b q` whose residues are `f`'s. -/
def Rel (b : Nat) (F : Poly) (f : VG.Spec.MlDsa.Poly) : Prop :=
  ∀ i < 256, F[i]!.val < b * q ∧ residue F[i]! = f[i]!

/-- A polynomial's coefficients as words. -/
def lift (f : VG.Spec.MlDsa.Poly) : Poly := f.map fun x => ⟨x.val, Nat.lt_trans x.isLt (by decide)⟩

theorem lift_get (f : VG.Spec.MlDsa.Poly) {i : Nat} (hi : i < 256) : ((lift f)[i]!).val = (f[i]!).val := by
  rw [getElem!_pos (lift f) i hi, lift, Vector.getElem_map, getElem!_pos f i hi]

theorem lift_rel (f : VG.Spec.MlDsa.Poly) : Rel 1 (lift f) f := by
  intro i hi
  have he := lift_get f hi
  refine ⟨by rw [he, Nat.one_mul]; exact f[i]!.isLt, Fin.ext ?_⟩
  rw [Fin.val_ofNat, he]; exact Nat.mod_eq_of_lt f[i]!.isLt

/-- A layer of the forward butterflies on words. -/
def layerB (F : Poly) (len : Nat) : Poly :=
  layF (fun f len k st t => blockN (bfly opB) f len (zetas k) st t) F len (fun c => 128 / len + c) (128 / len)

/-- The inverse butterfly with the negated zeta, as the code multiplies by
`negZetaTab`. -/
def opIBn (x y : Word) (z : Zq) : Word × Word := opIB x y (-z)

/-- A layer of the inverse butterflies on words. -/
def layerIB (F : Poly) (len : Nat) : Poly :=
  layF (fun f len k st t => blockN (bfly opIBn) f len (zetas k) st t) F len (fun c => 256 / len - 1 - c)
    (128 / len)

/-- The facts of the layers' sizes. -/
theorem len_facts {len : Nat} (hlen : len ∈ [1, 2, 4, 8, 16, 32, 64, 128]) :
    0 < len ∧ 2 * len * (128 / len) = 256 ∧
      ∀ i < 256, (i % (2 * len) < len → i + len < 256) ∧ (¬ i % (2 * len) < len → len ≤ i) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
  rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨by decide, by decide, ?_⟩
  all_goals intro i hi; omega

theorem nttLayer_eq (F : VG.Spec.MlDsa.Poly) (len : Nat) :
    Arith.nttLayer F len = Arith.layF (fun f len k st t => Arith.blockN Arith.bfly f len (zetas k) st t) F len
      (fun c => 128 / len + c) (128 / len) := rfl

theorem nttInvLayer_eq (F : VG.Spec.MlDsa.Poly) (len : Nat) :
    Arith.nttInvLayer F len = Arith.layF (fun f len k st t => Arith.blockN Arith.bflyInv f len (-zetas k) st t)
      F len (fun c => 256 / len - 1 - c) (128 / len) := rfl

theorem layerB_rel {b : Nat} (hb : b ≤ 15) {F : Poly} {f : VG.Spec.MlDsa.Poly} (hF : Rel b F f)
    {len : Nat} (hlen : len ∈ [1, 2, 4, 8, 16, 32, 64, 128]) :
    Rel (b + 2) (layerB F len) (Arith.nttLayer f len) := by
  have hl := len_facts hlen
  intro i hi
  rw [layerB, Arith.Lazy.layF_get (block_ok opB) F hl.1 _ (by omega) hi,
    nttLayer_eq, Arith.layF_get Arith.nttBlk_ok f hl.1 _ (by omega) hi]
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

theorem layerIB_rel {b : Nat} (hb : 1 ≤ b) (hb' : b ≤ 128) {F : Poly} {f : VG.Spec.MlDsa.Poly}
    (hF : Rel b F f) {len : Nat} (hlen : len ∈ [1, 2, 4, 8, 16, 32, 64, 128]) :
    Rel (2 * b) (layerIB F len) (Arith.nttInvLayer f len) := by
  have hl := len_facts hlen
  have lt : ∀ {x : Word}, x.val < b * q → x.val < 128 * q := fun h =>
    Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right q hb')
  intro i hi
  rw [layerIB, Arith.Lazy.layF_get (block_ok opIBn) F hl.1 _ (by omega) hi,
    nttInvLayer_eq, Arith.layF_get Arith.nttInvBlk_ok f hl.1 _ (by omega) hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    exact ⟨(opIB_bound _ _ (-_) hb hb' h0.1 h1.1).1, by
      rw [opIBn, (opIB_residue _ _ _ (lt h0.1) (lt h1.1)).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega)
    have h1 := hF i hi
    refine ⟨(opIB_bound _ _ (-_) hb hb' h0.1 h1.1).2, ?_⟩
    rw [opIBn, (opIB_residue _ _ _ (lt h0.1) (lt h1.1)).2, h0.2, h1.2]
    exact Arith.neg_mul_sub _ _ _

/-! ## Words in memory -/

/-- The words of `W` stored at `p`. -/
def LP (m : Mem) (p : Addr) (W : Poly) : Prop := ∀ i < n, (VG.Proof.MlDsa.coeffAt m p i).toNat = W[i]!.val

theorem lp_writeW {m : Mem} {p : Addr} {W : Poly} (h : LP m p W) {j : Nat} (hj : j < n) (x : Word)
    {v : BitVec 32} (hv : v.toNat = x.val) : LP (m.writeW (Arith.coeffAddr p j) v) p (W.set! j x) := by
  intro i hi
  rw [Arith.coeffAt_writeW m p hi hj]
  split
  · subst j; rw [Arith.Lazy.getElem!_set!_self _ hi, hv]
  · rw [Arith.Lazy.getElem!_set!_ne _ hi ‹_›, h i hi]

/-- A stored polynomial, as words. -/
theorem lp_lift {m : Mem} {p : Addr} {f : VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.PolyIs m p f) :
    LP m p (lift f) := fun i hi => by
  rw [Arith.polyIs_toNat h hi, lift_get f (by rw [n_eq] at hi; exact hi)]

/-- A word on 64 bits, loaded. -/
theorem w64_load {v : BitVec 32} {x : Word} (h : v.toNat = x.val) : v.setWidth 64 = w64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

/-- The low word of a value on 64 bits, stored. -/
theorem toW_store (v : BitVec 64) : (v.setWidth 32).toNat = (toW v).val := by
  rw [BitVec.toNat_setWidth, Fin.val_ofNat]

end VG.Proof.MlDsa.RISCV64.Arith.Lazy
