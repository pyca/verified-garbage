module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
public import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
public import VerifiedGarbage.Proof.MlKem.RISCV64.Reduce
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Reduce
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.MlDsa.Arith.Lazy
public import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MlDsa.Arith.Lazy
meta import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
meta import VerifiedGarbage.Proof.Framework.Omega

/-! ### `MlDsa.RISCV64.Arith.Lazy`, which this module and modules that import it used -/

section

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
  have e1 : z.val % 2 ^ 64 = z.val := Nat.mod_eq_of_lt (by omega_using [hz])
  have e2 : y.val % 2 ^ 64 = y.val := Nat.mod_eq_of_lt (by omega_using [])
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, e1, e2]
  have := Nat.mul_lt_mul_of_lt_of_le hz (Nat.le_of_lt hy) (by omega_using [])
  exact Nat.mod_eq_of_lt (by omega_using [this])

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
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])
  simp only [opB, toW, Fin.val_ofNat]
  unfold prod at ht ⊢
  generalize barv (z64 z * w64 y) = T at ht ⊢
  rw [q_eq] at hx ht ⊢
  constructor
  · rw [BitVec.toNat_add, hx', Nat.mod_eq_of_lt (by omega_using [hx, ht]), Nat.mod_eq_of_lt (by omega_using [ht])]
  · have e : (w64 x - T + 16760834).toNat = x.val + 16760834 - T.toNat := by
      generalize w64 x = X at hx' ⊢
      bv_omega
    rw [e, Nat.mod_eq_of_lt (by omega_using [hx])]

theorem opB_bound (x y : Word) (z : Zq) {b : Nat} (hb : b ≤ 15) (hx : x.val < b * q) :
    (opB x y z).1.val < (b + 2) * q ∧ (opB x y z).2.val < (b + 2) * q := by
  have hv := opB_values x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb))
  have ht := prod_lt y z
  rw [hv.1, hv.2, Nat.add_mul]
  omega_using [hx, ht]

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
    omega_using [ht']

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
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])
  have hy' : (w64 y).toNat = y.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := y.isLt; omega_using [])
  have hz : z.val < 8380417 := z.isLt
  have hx2 : x.val < 128 * 8380417 := hx
  have hy2 : y.val < 128 * 8380417 := hy
  have hd : (w64 x - w64 y + 1072693376).toNat = x.val + 1072693376 - y.val := by
    generalize w64 x = X at hx' ⊢
    generalize w64 y = Y at hy' ⊢
    bv_omega
  have hp : (z64 z * (w64 x - w64 y + 1072693376)).toNat = z.val * (x.val + 1072693376 - y.val) := by
    have e1 : z.val % 2 ^ 64 = z.val := Nat.mod_eq_of_lt (by omega_using [hz])
    rw [BitVec.toNat_mul, hd, BitVec.toNat_ofNat, e1]
    have := Nat.mul_lt_mul_of_lt_of_le hz (show x.val + 1072693376 - y.val ≤ 2 ^ 31 by omega_using [hx2]) (by omega_using [])
    exact Nat.mod_eq_of_lt (by omega_using [this])
  have hl := barv_lt (z64 z * (w64 x - w64 y + 1072693376))
  have hl2 : (barv (z64 z * (w64 x - w64 y + 1072693376))).toNat < 2 * 8380417 := hl
  refine ⟨?_, ?_, hl, ?_⟩
  · simp only [opIB, toW, Fin.val_ofNat]
    rw [BitVec.toNat_add, hx', hy', Nat.mod_eq_of_lt (by omega_using [hx2, hy2]), Nat.mod_eq_of_lt (by omega_using [])]
  · simp only [opIB, toW, Fin.val_ofNat, prodI]
    exact Nat.mod_eq_of_lt (by omega_using [hl2])
  · have := barv_mod (z64 z * (w64 x - w64 y + 1072693376))
    rw [hp] at this
    exact this

theorem opIB_bound (x y : Word) (z : Zq) {b : Nat} (hb : 1 ≤ b) (hb' : b ≤ 128) (hx : x.val < b * q)
    (hy : y.val < b * q) : (opIB x y z).1.val < 2 * b * q ∧ (opIB x y z).2.val < 2 * b * q := by
  have hv := opIB_values x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb'))
    (Nat.lt_of_lt_of_le hy (Nat.mul_le_mul_right q hb'))
  rw [hv.1, hv.2.1, Nat.mul_assoc]
  constructor
  · omega_using [hx, hy]
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
      rw [q_eq] at hx hy ⊢; omega_using [hy]
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
  all_goals intro i hi; omega_using [hi]

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
    have h0 := hF (i - len) (by omega_using [hi])
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
    have h0 := hF (i - len) (by omega_using [hi])
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
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])]

/-- The low word of a value on 64 bits, stored. -/
theorem toW_store (v : BitVec 64) : (v.setWidth 32).toNat = (toW v).val := by
  rw [BitVec.toNat_setWidth, Fin.val_ofNat]

end VG.Proof.MlDsa.RISCV64.Arith.Lazy

end

end

/-!
# ML-DSA on RISC-V: `vg_mldsa_ntt`

As ML-KEM's on RISC-V (`Proof/MlKem/RISCV64/Ntt.lean`), with ML-DSA's eight
layers (`Proof/MlDsa/Arith/Ntt.lean`), and lazy butterflies
(`Lazy.lean`): the table of the zetas stored (`setup_ok`); then the three
nested loops of `layerB`, `layF` and `blockN` on words
(`Proof/MlDsa/Arith/Lazy.lean`), with an invariant each (`LInv`, `BInv`,
`FInv`) saying which words `f` holds (`LP`); the butterfly is symbolically
executed once for any (aligned) pointers (`bfly_ok`), and stores the words
`opB` gives (`lp_bfly`). Layer `ℓ` has `len = 128 / 2^ℓ` and `2^ℓ` blocks.
The eight layers leave words less than `17 q` congruent to `NTT f`
(`nttLB_rel`), which the last loop reduces, coefficient by coefficient
(`CInv`, `cstep`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Arith.Ntt

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Arith
open VG.Impl.MlKem.RISCV64 (fixup)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.RISCV64.Arith
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ ptr_add ptr_ne lsr2 align4_add
  toNat_setWidth64 setWidth64_ofNat kept preserved_sub)
open VG.Proof.MlDsa.RISCV64.Arith.Lazy (LP lp_writeW lp_lift w64 w64_load toW toW_store z64 opB layerB Rel
  lift residue layerB_rel)

/-- Words of a polynomial. -/
abbrev LPoly := VG.Proof.MlDsa.Arith.Lazy.Poly

/-- The forward butterflies of a block, on words. -/
abbrev fblk : LPoly → Nat → Nat → Nat → Nat → LPoly := fun f len k st t =>
  VG.Proof.MlDsa.Arith.Lazy.blockN (VG.Proof.MlDsa.Arith.Lazy.bfly opB) f len (zetas k) st t

/-! ## Values -/

/-- A butterfly writes `f[j + len]`, then `f[j]`. -/
theorem lp_bfly {m : Mem} {F : Addr} {W : LPoly} (h : LP m F W) {j len : Nat}
    (hj : j + len < n) (z : Zq) {v₁ v₂ : BitVec 32} (h₁ : v₁.toNat = (opB W[j]! W[j + len]! z).2.val)
    (h₂ : v₂.toNat = (opB W[j]! W[j + len]! z).1.val) :
    LP ((m.writeW (coeffAddr F (j + len)) v₁).writeW (coeffAddr F j) v₂) F
      (VG.Proof.MlDsa.Arith.Lazy.bfly opB W j len z) :=
  lp_writeW (lp_writeW h hj _ h₁) (by omega_arith) _ h₂

/-! ## Loops on two pointers -/

/-- A `do … while (a ≠ b)` loop whose body runs `N` times: iteration `i`
keeps the invariant, and leaves `a ≠ b` exactly when it is not the last. -/
theorem wp_loop_ne {body : Prog isa} {a b : Reg} {Q : State → Prop} (Inv : Nat → State → Prop) {N : Nat}
    (hN : 0 < N)
    (hstep : ∀ i < N, ∀ s, Inv i s →
      WP isa body s (fun s' => Inv (i + 1) s' ∧ (s'.gpr a != s'.gpr b) = decide (i + 1 ≠ N)))
    (hQ : ∀ s, Inv N s → Q s) {s₀ : State} (h0 : Inv 0 s₀) : WP isa (.loop body (.ne a b)) s₀ Q := by
  let I : Nat → State → Prop := fun n s => ∃ i, i < N ∧ n = N - i ∧ Inv i s
  have hI : I N s₀ := ⟨0, hN, (Nat.sub_zero N).symm, h0⟩
  refine WP.loop (M := isa) (body := body) (c := .ne a b) (Q := Q) I ?_ N s₀ hI
  rintro n s ⟨i, hi, rfl, hs⟩
  refine WP.mono (hstep i hi s hs) fun s' ⟨hs', hz⟩ => ?_
  have ev : isa.eval (.ne a b) s' = some (decide (i + 1 ≠ N)) := by
    show (some (s'.gpr a != s'.gpr b) : Option Bool) = _
    rw [hz]
  by_cases h : i + 1 = N
  · refine .inl ⟨by rw [ev]; simp [h], hQ s' (h ▸ hs')⟩
  · exact .inr ⟨by rw [ev]; simp [h], N - (i + 1), by omega_using [hi], i + 1, by omega_using [hi, h], rfl, hs'⟩

/-- Two pointers into the same buffer differ exactly when their offsets do. -/
theorem ptr_bne (p : BitVec 64) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (p + BitVec.ofNat 64 a != p + BitVec.ofNat 64 b) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have h2 : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun e => h (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)
    have h3 : p + BitVec.ofNat 64 a ≠ p + BitVec.ofNat 64 b := fun e => h2 (by
      have := congrArg (· - p) e
      simpa using this)
    simp [h3, h]

/-! ## The butterfly -/

section
variable {s : State} {x z : BitVec 64} {o : Nat}

theorem bfly_ok (ho : o < 2048) (h5 : s.gpr .a2 = x) (h7 : s.gpr .a4 = z) (h8 : s.gpr .a5 = 2201172575745)
    (h9 : s.gpr .a6 = 8380417) (h12 : s.gpr .t5 = 16760834)
    (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 o) 4)
    (oa : InRegions s.wr x 4) (ob : InRegions s.wr (x + BitVec.ofNat 64 o) 4) (ax : x.toNat % 4 = 0)
    (ay : (x + BitVec.ofNat 64 o).toNat % 4 = 0) :
    WP isa (.block (bflyBody o)) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .a3 = s.gpr .a3 ∧ s'.gpr .a0 = s.gpr .a0 ∧
      s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a4 = z ∧ s'.gpr .a5 = 2201172575745 ∧ s'.gpr .a6 = 8380417 ∧
      s'.gpr .t5 = 16760834 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW (x + BitVec.ofNat 64 o) (((s.mem.readW x 32).setWidth 64 -
            barv (z * (s.mem.readW (x + BitVec.ofNat 64 o) 32).setWidth 64) + 16760834).setWidth 32)).writeW x
          (((s.mem.readW x 32).setWidth 64 +
            barv (z * (s.mem.readW (x + BitVec.ofNat 64 o) 32).setWidth 64)).setWidth 32) := by
  rw [show bflyBody o = ([.load .w .t2 .a2 0, .load .w .t0 .a2 o, .mul .t0 .a4 .t0] : List Instr) ++
    (barrett .t0 .t3 ++ ([.sub .t3 .t2 .t0, .add .t3 .t3 .t5, .store .w .t3 .a2 o, .add .t2 .t2 .t0,
      .store .w .t2 .a2 0, .addi .a2 .a2 4] : List Instr)) by
      simp only [bflyBody, List.cons_append, List.nil_append]]
  refine WP.block_append ?_
  crun [ho, h5, h7, ia, ib, ax, ay]
  refine barrett_ok (by decide) (by decide) (by simp [h8]) (by simp [h9]) fun s' k => ?_
  have g := k.other
  crun [ho, kept, k.gpr, g, k.mem, k.rd, k.wr, k.sp, h5, h7, h8, h9, h12, oa, ob, ax, ay,
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
  tab : ∀ j < 256, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (zetaTab j)
  poly : PolyIs m₁ (F s₀) (P s₀)

/-- What every loop keeps, with the constant `k5` in `t5`. -/
structure Env (k5 : BitVec 64) (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  a0 : s.gpr .a0 = F s₀ + BitVec.ofNat 64 1024
  a5 : s.gpr .a5 = 2201172575745
  a6 : s.gpr .a6 = 8380417
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

/-- After `t` butterflies of the block from `st` with the zeta `zetas k` of
the layer with `len`, from `Q`: the zeta pointer is at `k + 1`, and `a3` at
the end of the block's first half. -/
structure FInv (s₀ : State) (m₁ : Mem) (Q : LPoly) (len k st : Nat) (t : Nat) (s : State) : Prop where
  env : Env 16760834 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (k + 1))
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (st + t))
  a3 : s.gpr .a3 = F s₀ + BitVec.ofNat 64 (4 * (st + len))
  a4 : s.gpr .a4 = BitVec.ofNat 64 (zetas k).val
  poly : LP s.mem (F s₀) (fblk Q len k st t)

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {Q : LPoly} {len k st t : Nat} (hl : 4 * len < 2048)
    (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : FInv s₀ m₁ Q len k st t s) :
    WP isa (.block (bflyBody (4 * len))) s fun s' =>
      FInv s₀ m₁ Q len k st (t + 1) s' ∧ (s'.gpr .a2 != s'.gpr .a3) = decide (t + 1 ≠ len) := by
  have ea : F s₀ + BitVec.ofNat 64 (4 * (st + t)) = coeffAddr (F s₀) (st + t) := rfl
  have eb : F s₀ + BitVec.ofNat 64 (4 * (st + t)) + BitVec.ofNat 64 (4 * len) =
      coeffAddr (F s₀) (st + t + len) := by
    rw [ptr_add, show 4 * (st + t) + 4 * len = 4 * (st + t + len) by omega_arith]
  have ca := coeff_contains (F s₀) (i := st + t) (by rw [n_eq]; omega_arith)
  have cb := coeff_contains (F s₀) (i := st + t + len) (by rw [n_eq]; omega_arith)
  have va := h.poly (st + t) (by rw [n_eq]; omega_arith)
  have vb := h.poly (st + t + len) (by rw [n_eq]; omega_arith)
  refine WP.mono (bfly_ok hl h.a2 h.a4 h.env.a5 h.env.a6 h.env.t5
    (by rw [ea]; exact h.env.inR hp ca) (by rw [eb]; exact h.env.inR hp cb)
    (by rw [ea]; exact h.env.inW hp ca) (by rw [eb]; exact h.env.inW hp cb)
    (align4_add hp.alF _) (by rw [eb]; exact align4_add hp.alF _))
    fun s' ⟨r5, r6, r3, r4, r7, r8, r9, r12, kp, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.a0, r8, r9, r12, fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
        wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, r4.trans h.a1, ?_, r6.trans h.a3, r7, ?_⟩, ?_⟩
  · rw [m, eb, ea]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ cb).writeW (List.mem_singleton_self _) _ ca
  · rw [r5, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [m, eb, ea, ← coeffAt_eq, ← coeffAt_eq, w64_load va, w64_load vb,
      show fblk Q len k st (t + 1) = VG.Proof.MlDsa.Arith.Lazy.bfly opB (fblk Q len k st t) (st + t) len (zetas k)
        from VG.Proof.MlDsa.Arith.Lazy.blockN_succ _ _ _ _ _ _]
    exact lp_bfly h.poly (by rw [n_eq]; omega_arith) _ (toW_store _) (toW_store _)
  · have e2 : s'.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (st + t + 1)) := by rw [r5]; exact ptr_succ _ 4 _
    rw [e2, r6, h.a3, ptr_bne _ (by omega_arith) (by omega_arith)]
    exact decide_eq_decide.mpr ⟨fun e e' => e (by omega_arith), fun e e' => e (by omega_arith)⟩

/-! ## Blocks -/

section
variable {s : State} {x4 x5 y : BitVec 64} {o : Nat}

/-- The start of a block: its zeta, and the end of its first half. -/
theorem bpre_ok (ho : o < 2048) (h4 : s.gpr .a1 = x4) (h5 : s.gpr .a2 = x5)
    (i4 : InRegions (s.rd ++ s.wr) x4 4) (a4 : x4.toNat % 4 = 0) :
    WP isa (.block [.load .w .a4 .a1 0, .addi .a1 .a1 4, .addi .a3 .a2 o]) s
      fun s' => s'.gpr .a4 = (s.mem.readW x4 32).setWidth 64 ∧ s'.gpr .a1 = x4 + 4 ∧
        s'.gpr .a3 = x5 + BitVec.ofNat 64 o ∧ s'.gpr .a2 = x5 ∧
        s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine Steps.wp_lwu (a := x4) (by decide) (by rw [h4]; simp) a4 i4 fun s₁ u₁ =>
    Steps.wp_addi (by decide) fun s₂ u₂ => Steps.wp_addi ho fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .a4 → r ≠ .a1 → r ≠ .a3 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  refine ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h4]; rfl,
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h5],
    by rw [g _ (by decide) (by decide) (by decide), h5],
    g _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide),
    g _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide),
    fun r hr => g r (by revert r; decide) (by revert r; decide) (by revert r; decide),
    by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr],
    by rw [u₃.sp, u₂.sp, u₁.sp]⟩

/-- The end of a block: the next block's start. -/
theorem bpost_ok (ho : o < 2048) (h5 : s.gpr .a2 = y) :
    WP isa (.block [.addi .a2 .a2 o]) s fun s' =>
      s'.gpr .a2 = y + BitVec.ofNat 64 o ∧ s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a1 = s.gpr .a1 ∧
        s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine Steps.wp_addi ho fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, h5], u₁.other _ (by decide),
    u₁.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide),
    fun r hr => u₁.other r (by revert r; decide), u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩

end

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : LPoly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : Env 16760834 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (nb + c))
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (2 * len * c))
  poly : LP s.mem (F s₀) (VG.Proof.MlDsa.Arith.Lazy.layF fblk Q len (fun c => 128 / len + c) c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {Q : LPoly} {len nb c : Nat}
    (hl : 0 < len) (ho : 4 * len < 2048) (hnb : len * nb = 128) (hc : c < nb) {s : State}
    (h : BInv s₀ m₁ Q len nb c s) :
    WP isa (nttBlockCode (4 * len)) s fun s' =>
      BInv s₀ m₁ Q len nb (c + 1) s' ∧ (s'.gpr .a2 != s'.gpr .a0) = decide (c + 1 ≠ nb) := by
  have hdiv : 128 / len = nb := by rw [← hnb, Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  have hk : nb + c < 256 := by
    have : nb ≤ len * nb := Nat.le_mul_of_pos_left nb hl
    omega_arith
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * (nb + c))) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have vz : (s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * (nb + c))) 32).setWidth 64 =
      BitVec.ofNat 64 (zetas (128 / len + c)).val := by
    have ez : zetaTab (nb + c) = (zetas (nb + c)).val := zetaNat_eq (nb + c)
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), hm.tab _ hk, hdiv, ez, setWidth64_ofNat (by have := val_lt (zetas (nb + c)); omega_arith)]
  refine WP.seq (WP.mono (bpre_ok ho h.a1 h.a2 (h.env.inRS hp cS) (align4_add (by have := hp.alS; omega_using [this]) _))
    fun s₁ ⟨r7, r4, r6, r5, r3, r8, r9, r12, kp, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : FInv s₀ m₁ (VG.Proof.MlDsa.Arith.Lazy.layF fblk Q len (fun c => 128 / len + c) c) len
      (128 / len + c) (2 * len * c) 0 s₁ := by
    refine ⟨⟨r3.trans h.env.a0, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5,
      fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, ?_, ?_, ?_, m ▸ h.poly⟩
    · rw [r4, hdiv]
      exact (ptr_add _ _ 4).trans (by rw [show 4 * (nb + c) + 4 = 4 * (nb + c + 1) by omega_arith])
    · rw [r5, Nat.add_zero]
    · rw [r6, ptr_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len) by omega_arith]
    · rw [r7, vz]
  refine wp_loop_ne (FInv s₀ m₁ (VG.Proof.MlDsa.Arith.Lazy.layF fblk Q len (fun c => 128 / len + c) c) len
    (128 / len + c) (2 * len * c)) hl (fun t ht s h => fstep hp ho (by omega_arith) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (bpost_ok ho h₂.a2) fun s' ⟨r5, r3, r4, r8, r9, r12, kp, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.a0, r8.trans h₂.env.a5, r9.trans h₂.env.a6, r12.trans h₂.env.t5,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r4, h₂.a1, hdiv, Nat.add_assoc]
  · rw [r5, ptr_add]; congr 2; rw [Nat.mul_succ]; omega_arith
  · rw [m, VG.Proof.MlDsa.Arith.Lazy.layF, foldl_range_succ, ← VG.Proof.MlDsa.Arith.Lazy.layF]
    exact h₂.poly
  · rw [r5, r3, h₂.env.a0, ptr_add, show (1024 : Nat) = 4 * 256 from rfl,
      ptr_bne _ (by omega_arith) (by omega_arith)]
    refine decide_eq_decide.mpr ⟨fun e e' => e ?_, fun e e' => e ?_⟩
    · subst e'; rw [Nat.mul_add, Nat.mul_one] at *; omega_arith
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega_arith
      exact Nat.eq_of_mul_eq_mul_left hl this

/-! ## Layers -/

/-- The first `ℓ` layers of `NTT`. -/
def nttL (ℓ : Nat) (w : Poly) : Poly := (nttLens.take ℓ).foldl nttLayer w

theorem nttL_succ (w : Poly) {ℓ : Nat} (hℓ : ℓ < 8) : nttL (ℓ + 1) w = nttLayer (nttL ℓ w) (128 >>> ℓ) := by
  have e : nttLens[ℓ]'(by simp [nttLens]; omega_arith) = 128 >>> ℓ := by
    revert ℓ; decide
  unfold nttL
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simp [nttLens]; omega_arith), e]
  rfl

theorem ntt_eq_nttL (w : Poly) : ntt w = nttL 8 w := by
  rw [ntt_eq_layers]; rfl

/-- The first `ℓ` layers of the butterflies on words. -/
def nttLB (ℓ : Nat) (W : LPoly) : LPoly := (nttLens.take ℓ).foldl layerB W

theorem nttLB_succ (W : LPoly) {ℓ : Nat} (hℓ : ℓ < 8) : nttLB (ℓ + 1) W = layerB (nttLB ℓ W) (128 >>> ℓ) := by
  have e : nttLens[ℓ]'(by simp [nttLens]; omega_arith) = 128 >>> ℓ := by
    revert ℓ; decide
  unfold nttLB
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simp [nttLens]; omega_arith), e]
  rfl

theorem len_mem : ∀ ℓ < 8, 128 >>> ℓ ∈ [1, 2, 4, 8, 16, 32, 64, 128] := by decide

/-- After `ℓ` layers, words less than `(2ℓ + 1) q` congruent to the
specification's. -/
theorem nttLB_rel (f : Poly) : ∀ ℓ ≤ 8, Rel (2 * ℓ + 1) (nttLB ℓ (lift f)) (nttL ℓ f)
  | 0, _ => Lazy.lift_rel f
  | ℓ + 1, h => by
    rw [nttLB_succ _ (by omega_arith), nttL_succ _ (by omega_arith)]
    exact layerB_rel (by omega_arith) (nttLB_rel f ℓ (by omega_arith)) (len_mem ℓ (by omega_arith))

/-- What the layers' loops count: layer `ℓ` has `len = 128 >>> ℓ` and `2^ℓ`
blocks, and its code is the `ℓ`-th of `nttOffs`. -/
theorem layer_facts : ∀ ℓ < 8, 0 < 128 >>> ℓ ∧ (128 >>> ℓ) * 2 ^ ℓ = 128 ∧ 0 < 2 ^ ℓ ∧
    2 ^ ℓ + 2 ^ ℓ = 2 ^ (ℓ + 1) ∧ 128 / (128 >>> ℓ) = 2 ^ ℓ ∧ 4 * (128 >>> ℓ) < 2048 ∧
    nttOffs.drop ℓ = 4 * (128 >>> ℓ) :: nttOffs.drop (ℓ + 1) := by
  decide

section
variable {s : State} {x3 : BitVec 64}

theorem lpre_ok (h3 : s.gpr .a0 = x3) :
    WP isa (.block [.addi .a2 .a0 (-1024)]) s fun s' =>
      s'.gpr .a2 = x3 - 1024 ∧ s'.gpr .a0 = x3 ∧ s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a5 = s.gpr .a5 ∧
        s'.gpr .a6 = s.gpr .a6 ∧ s'.gpr .t5 = s.gpr .t5 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h3, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

end

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : Env 16760834 s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * 2 ^ ℓ)
  poly : LP s.mem (F s₀) (nttLB ℓ (lift (P s₀)))

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 8) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa (nttLayerCode (4 * (128 >>> ℓ))) s (LInv s₀ m₁ (ℓ + 1)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, -⟩ := layer_facts ℓ hℓ
  refine WP.seq (WP.mono (lpre_ok h.env.a0)
    fun s₁ ⟨r5, r3, r4, r8, r9, r12, kp, m, rd, wr, sp⟩ => ?_)
  have h₁ : BInv s₀ m₁ (nttLB ℓ (lift (P s₀))) (128 >>> ℓ) (2 ^ ℓ) 0 s₁ := by
    refine ⟨⟨r3, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5, fun r hr => (kp r hr).trans (h.env.kept r hr),
      rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩,
      by rw [r4, h.a1, Nat.add_zero], ?_, ?_⟩
    · rw [r5, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_ne (BInv s₀ m₁ (nttLB ℓ (lift (P s₀))) (128 >>> ℓ) (2 ^ ℓ)) f3
    (fun c hc s h => bstep hp hm f1 f6 f2 hc h) (fun s₂ h₂ => ⟨h₂.env, ?_, ?_⟩) h₁
  · rw [h₂.a1, f4]
  · rw [nttLB_succ _ hℓ, layerB]
    exact (congrArg (fun b => LP s₂.mem (F s₀) (VG.Proof.MlDsa.Arith.Lazy.layF fblk (nttLB ℓ (lift (P s₀)))
      (128 >>> ℓ) (fun c => 128 / (128 >>> ℓ) + c) b)) f5).mpr h₂.poly

/-- The layers from `ℓ` on. -/
theorem layers_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) :
    ∀ j ℓ, ℓ + j = 8 → ∀ s, LInv s₀ m₁ ℓ s → WP isa (layers nttLayerCode (nttOffs.drop ℓ)) s (LInv s₀ m₁ 8)
  | 0, ℓ, h, s, hs => by
    obtain rfl : ℓ = 8 := by omega_using [h]
    exact WP.block_nil hs
  | j + 1, ℓ, h, s, hs => by
    have hℓ : ℓ < 8 := by omega_using [h]
    rw [(layer_facts ℓ hℓ).2.2.2.2.2.2]
    exact WP.seq (WP.mono (lstep hp hm hℓ hs) fun s' h' => layers_ok hp hm j (ℓ + 1) (by omega_using [h]) s' h')

/-! ## Setup and the end -/

theorem sub_low (p : Addr) {k L : Nat} (h : k ≤ L) : Region.Sub ⟨p, k⟩ ⟨p, L⟩ := fun a ha => by
  simp only [Region.Contains] at ha ⊢; omega_arith

/-- The table stored in `scratch`. -/
theorem setup_base {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table zetaTab .a1)) s₀ fun s =>
      Setup s₀ s.mem ∧ (∀ r, r ≠ .t2 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
        s.sp = s₀.sp := by
  have fS := hp.fitS
  have wS : ∀ {o k : Nat}, o + k ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) k := fun h => by
    rw [hp.wr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_arith)⟩
  have a8 : (s₀.gpr .a1).toNat % 8 = 0 := hp.alS
  refine WP.mono (table_ok zetaTab zetaTab_lt (b := .a1) (by decide) rfl
    (by omega_using [a8]) fun k hk => wS (by omega_arith)) fun s₂ h₂ => ?_
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    refine h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    rw [List.mem_singleton] at hr; subst hr
    exact sub_low _ (by omega_arith)
  exact ⟨⟨fun j hj => h₂.tab j hj, polyIs_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj) ⟨hp.red, rfl⟩⟩,
    h₂.gpr, h₂.rd, h₂.wr, h₂.sp⟩

theorem tail_ok {s : State} :
    WP isa (.block (consts ++ ([.add .t5 .a6 .a6, .addi .a0 .a0 1024, .addi .a1 .a1 4] : List Instr))) s
      fun s' => s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 1024 ∧ s'.gpr .a1 = s.gpr .a1 + 4 ∧
        s'.gpr .a5 = 2201172575745 ∧ s'.gpr .a6 = 8380417 ∧ s'.gpr .t5 = 16760834 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [consts, loadM_eq, loadImm_q, List.cons_append, List.nil_append]
  crun [kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table zetaTab .a1 ++ consts ++
      ([.add .t5 .a6 .a6, .addi .a0 .a0 1024, .addi .a1 .a1 4] : List Instr))) s₀
      fun s => Setup s₀ s.mem ∧ LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  refine WP.mono tail_ok fun s ⟨r3, r4, r8, r9, r12, kp, m, rd', wr', sp'⟩ => ?_
  rw [m]
  refine ⟨hm, ⟨⟨by rw [r3, e .a0 (by decide)], r8, r9, r12, fun r hr => ?_, rd'.trans rd,
    wr'.trans wr, sp'.trans sp, by rw [m]; exact Frame.refl _ _⟩,
    by rw [r4, e .a1 (by decide)]; rfl, m ▸ lp_lift hm.poly⟩⟩
  rw [kp r hr, e r (by revert r hr; decide)]

/-! ## The reduction -/

/-- The first `i` words of `W` reduced modulo `q`. -/
def canonN (W : LPoly) (i : Nat) : LPoly :=
  (List.range i).foldl (fun w j => w.set! j (Fin.ofNat _ (w[j]!.val % q))) W

theorem canonN_zero (W : LPoly) : canonN W 0 = W := rfl

/-- A word reduced modulo `q`, as `reduce` stores it. -/
theorem red_store (x : VG.Proof.MlDsa.Arith.Lazy.Word) :
    ((red (w64 x)).setWidth 32).toNat = (Fin.ofNat 4294967296 (x.val % q) : VG.Proof.MlDsa.Arith.Lazy.Word).val := by
  have hx := x.isLt
  have hq : x.val % q < 2 ^ 32 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  have hw : (w64 x).toNat = x.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [])
  rw [BitVec.toNat_setWidth, red_toNat, hw, Fin.val_ofNat, Nat.mod_eq_of_lt hq]

theorem canonN_succ (W : LPoly) (i : Nat) :
    canonN W (i + 1) = (canonN W i).set! i (Fin.ofNat _ ((canonN W i)[i]!.val % q)) :=
  foldl_range_succ _ _ _

theorem canonN_get (W : LPoly) : ∀ i ≤ n, ∀ j < n,
    (canonN W i)[j]! = if j < i then Fin.ofNat _ (W[j]!.val % q) else W[j]!
  | 0, _, j, _ => by rw [ite_eq_right (Nat.not_lt_zero j)]; rfl
  | i + 1, hi, j, hj => by
    have ih := canonN_get W i (by omega_arith)
    rw [canonN_succ]
    by_cases e : i = j
    · subst e
      rw [VG.Proof.MlDsa.Arith.Lazy.getElem!_set!_self _ hj, ih i hj, ite_eq_right (Nat.lt_irrefl i),
        ite_eq_left (Nat.lt_succ_self i)]
    · rw [VG.Proof.MlDsa.Arith.Lazy.getElem!_set!_ne _ hj e, ih j hj]
      by_cases hji : j < i
      · rw [ite_eq_left hji, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hji, ite_eq_right (by omega_arith)]

/-- After `i` words of `W` reduced. -/
structure CInv (s₀ : State) (m₁ : Mem) (W : LPoly) (i : Nat) (s : State) : Prop where
  env : Env 16760834 s₀ m₁ s
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * i)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (256 - i)
  poly : LP s.mem (F s₀) (canonN W i)

section
variable {s : State} {x c : BitVec 64}

theorem canon_ok (h5 : s.gpr .a2 = x) (h8 : s.gpr .a5 = 2201172575745)
    (h9 : s.gpr .a6 = 8380417) (h11 : s.gpr .t1 = c)
    (ia : InRegions (s.rd ++ s.wr) x 4) (oa : InRegions s.wr x 4) (ax : x.toNat % 4 = 0) :
    WP isa (.block canonBody) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a0 = s.gpr .a0 ∧
      s'.gpr .a5 = 2201172575745 ∧ s'.gpr .a6 = 8380417 ∧ s'.gpr .t5 = s.gpr .t5 ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW x ((red ((s.mem.readW x 32).setWidth 64)).setWidth 32) := by
  rw [show canonBody = ([.load .w .t2 .a2 0] : List Instr) ++ (reduce .t2 .t3 ++
      ([.store .w .t2 .a2 0, .addi .a2 .a2 4, .addi .t1 .t1 (-1)] : List Instr)) by
    simp only [canonBody, List.cons_append, List.nil_append]]
  refine WP.block_append ?_
  crun [h5, ia, ax]
  refine reduce_ok (by decide) (by decide) (by decide) (by simp [h8]) (by simp [h9])
    fun s' k => ?_
  have g := k.other
  crun [kept, k.gpr, g, k.mem, k.rd, k.wr, k.sp, h5, h8, h9, h11, oa, ax,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

theorem cstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {W : LPoly} {i : Nat} (hi : i < 256) {s : State}
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

/-- Words less than `17 q`, each reduced: the polynomial they are congruent to. -/
theorem canon_full {m : Mem} {p : Addr} {W : LPoly} {f : Poly} (hr : Rel 17 W f) (h : LP m p (canonN W 256)) :
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
      s.gpr .ra = s₀.gpr .ra ∧ PolyIs s.mem (F s₀) (Spec.MlDsa.ntt (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => ?_)
  refine WP.seq (WP.mono (layers_ok hp hm 8 0 rfl s₁ h₁) fun s h => ?_)
  refine WP.seq (WP.mono cpre_ok fun s₂ ⟨r5, r11, r3, r8, r9, r12, kp, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_nz (CInv s₀ s₁.mem (nttLB 8 (lift (P s₀)))) (N := 256) (by decide)
    (fun i hi s h => cstep hp hi h) (fun s' h' => ⟨fun r hr => h'.env.kept r (preserved_sub r hr), h'.env.sp,
      h'.env.kept .ra (by decide), by
        rw [ntt_eq_nttL]; exact canon_full (nttLB_rel (P s₀) 8 (by decide)) h'.poly⟩) ?_
  refine ⟨⟨r3.trans h.env.a0, r8.trans h.env.a5, r9.trans h.env.a6, r12.trans h.env.t5,
    fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
    wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, r11, ?_⟩
  · rw [r5, h.env.a0, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
  · rw [m, canonN_zero]; exact h.poly

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.nttContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, RISCV64.abi,
    RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem verified : Verified RISCV64.target ntt (Proof.MlDsa.nttContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.RISCV64.Add.ctRegs [.a0, .a1] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hra, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hra⟩, ?_⟩
    sig_post [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs]
    exact h
  · sig_pub [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, RISCV64.abi,
        RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact AddSub.reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Arith.Ntt
