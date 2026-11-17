module

public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.Arith.Lazy
public import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.Framework.Range

/-! ### `MlDsa.Arm.Arith.NttBfly`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: the butterflies of `NTT` and `NTT⁻¹`

The butterflies of `Impl/MlDsa/Arm/Arith/Ntt.lean` reduce only the product,
to `mulz`'s value (`bprod`, at most `redMax < 2q`), and store the sum and
the difference as they are: the coefficients between layers are words
(`Proof/MlDsa/Arith/Lazy.lean`'s `Word`) congruent to the specification's,
and bounded by a multiple of `q` that grows with each layer, as on RISC-V
(`Proof/MlDsa/RISCV64/Arith/Lazy.lean`).

* `opF` is what the forward butterfly stores, `(x + t, x + 2q - t)` for the
  reduced product `t` of `y` and the zeta, on 32 bits, so that the stores
  are `opF` for every input; for `x < 15q` it is that sum and difference
  (`opF_values`), less than `2q` more than `x` and congruent to the
  specification's butterfly (`opF_bound`, `opF_residue`). A layer then takes
  `Rel b` to `Rel (b + 2)` (`layerF_rel`): eight layers from `Rel 1` end at
  `Rel 17`.
* `opI` is the inverse butterfly's, `(x + y, t)` for the reduced product `t`
  of the zeta and `x + 128q - y`: for `x, y < b q` with `b ≤ 128`, that sum
  and a product below `2q` (`opI_values`), so a layer takes `Rel b` to
  `Rel 2b` (`layerI_rel`), and eight layers from `Rel 1` end at `Rel 256`,
  every coefficient less than `256 q < 2³¹`.

Each butterfly is three blocks, each symbolically executed once for any state:
before `mulz`, `mulz` (`mulz_ok`), and after it; they store `opF` and `opI`
of the two words (`bfly_spec`, `bflyInv_spec`): what `BflyOk` states of a
butterfly's code, for the loops (`NttLoop.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Arith

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq zetas)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.Arm (addr_ptr inRegions_of)

/-! ## Words -/

/-- A word between layers. -/
abbrev Word := VG.Proof.MlDsa.Arith.Lazy.Word

/-- The words of a polynomial. -/
abbrev LPoly := VG.Proof.MlDsa.Arith.Lazy.Poly

/-- A word, in a register. -/
abbrev wb (x : Word) : BitVec 32 := BitVec.ofNat 32 x.val

/-- A register's value, as a word. -/
abbrev toW (v : BitVec 32) : Word := Fin.ofNat _ v.toNat

/-- A zeta, in a register. -/
abbrev zb (z : Zq) : BitVec 32 := BitVec.ofNat 32 z.val

/-- The residue of a word. -/
abbrev residue (x : Word) : Zq := Fin.ofNat q x.val

theorem wb_toNat (x : Word) : (wb x).toNat = x.val := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.isLt

theorem toW_val (v : BitVec 32) : (toW v).val = v.toNat := by
  rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt v.isLt

/-- A register that holds the word `x`. -/
theorem wb_of {v : BitVec 32} {x : Word} (h : v.toNat = x.val) : v = wb x :=
  BitVec.eq_of_toNat_eq (by rw [wb_toNat, h])

/-- The reduced product of `y` and the zeta `z`, as `mulz` leaves it. -/
abbrev bprod (y : BitVec 32) (z : Zq) : BitVec 32 := bmulz y (zb z) (bquot (zb z))

theorem bprod_toNat (y : BitVec 32) (z : Zq) : (bprod y z).toNat = mulzN y.toNat z.val := by
  rw [bmulz_toNat y (by rw [toNat_val]; exact z.isLt), toNat_val]

/-! ## The forward butterfly -/

/-- The reduced product of the word `y` and the zeta. -/
def prodF (y : Word) (z : Zq) : Nat := mulzN y.val z.val

theorem prodF_lt (y : Word) (z : Zq) : prodF y z < 2 * q :=
  Nat.lt_of_le_of_lt (mulzN_le y.isLt z.isLt) redMax_lt

theorem prodF_mod (y : Word) (z : Zq) : prodF y z % q = z.val * y.val % q := by
  rw [prodF, mulzN_mod y.isLt z.isLt, Nat.mul_comm]

/-- What the forward butterfly stores: `x + t` and `x + 2q - t`, as words. -/
def opF (x y : Word) (z : Zq) : Word × Word :=
  (toW (wb x + bprod (wb y) z), toW (wb x + 16760834 - bprod (wb y) z))

theorem opF_values (x y : Word) (z : Zq) (hx : x.val < 15 * q) :
    (opF x y z).1.val = x.val + prodF y z ∧ (opF x y z).2.val = x.val + 2 * q - prodF y z := by
  have ht : prodF y z < 2 * 8380417 := prodF_lt y z
  have e := bprod_toNat (wb y) z
  rw [wb_toNat] at e
  have hx' := wb_toNat x
  simp only [opF, toW_val]
  unfold prodF at ht ⊢
  generalize mulzN y.val z.val = P at e ht ⊢
  generalize bprod (wb y) z = T at e ⊢
  generalize wb x = X at hx' ⊢
  rw [q_eq] at hx ⊢
  constructor <;> bv_omega

theorem opF_bound (x y : Word) (z : Zq) {b : Nat} (hb : b ≤ 15) (hx : x.val < b * q) :
    (opF x y z).1.val < (b + 2) * q ∧ (opF x y z).2.val < (b + 2) * q := by
  have hv := opF_values x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb))
  have ht := prodF_lt y z
  rw [hv.1, hv.2, Nat.add_mul]
  omega_using [hx, ht]

theorem opF_residue (x y : Word) (z : Zq) (hx : x.val < 15 * q) :
    residue (opF x y z).1 = residue x + z * residue y ∧
    residue (opF x y z).2 = residue x - z * residue y := by
  have hv := opF_values x y z hx
  have ht := prodF_lt y z
  have hm' : (z * residue y).val = prodF y z % q := by
    rw [Fin.val_mul, residue, Fin.val_ofNat, Nat.mul_mod_mod, prodF_mod]
  constructor
  · apply Fin.ext
    rw [Fin.val_add, hm']
    change (opF x y z).1.val % q = (x.val % q + prodF y z % q) % q
    rw [hv.1, Nat.add_mod]
  · apply Fin.ext
    rw [Fin.val_sub, hm']
    change (opF x y z).2.val % q = (q - prodF y z % q + x.val % q) % q
    rw [hv.2]
    have ht' : prodF y z < 2 * 8380417 := ht
    change (x.val + 2 * 8380417 - prodF y z) % 8380417 =
      (8380417 - prodF y z % 8380417 + x.val % 8380417) % 8380417
    omega_using [ht']

/-! ## The inverse butterfly -/

/-- The reduced product of the zeta and `x + 128 q - y`. -/
def prodI (x y : Word) (z : Zq) : Nat := mulzN (x.val + 128 * q - y.val) z.val

/-- What the inverse butterfly stores: `x + y`, and the reduced product of
the zeta and `x + 128 q - y`, as words. -/
def opI (x y : Word) (z : Zq) : Word × Word :=
  (toW (wb x + wb y), toW (bprod (wb x + 1072693376 - wb y) z))

theorem opI_values (x y : Word) (z : Zq) (hx : x.val < 128 * q) (hy : y.val < 128 * q) :
    (opI x y z).1.val = x.val + y.val ∧ (opI x y z).2.val = prodI x y z ∧
      prodI x y z < 2 * q ∧ prodI x y z % q = z.val * (x.val + 128 * q - y.val) % q := by
  have hx' := wb_toNat x
  have hy' := wb_toNat y
  have hx2 : x.val < 128 * 8380417 := hx
  have hy2 : y.val < 128 * 8380417 := hy
  have hd : (wb x + 1072693376 - wb y).toNat = x.val + 128 * q - y.val := by
    rw [q_eq]
    generalize wb x = X at hx' ⊢
    generalize wb y = Y at hy' ⊢
    bv_omega
  have hlt : x.val + 128 * q - y.val < 2 ^ 32 := by rw [q_eq]; omega_using [hx2]
  refine ⟨?_, ?_, Nat.lt_of_le_of_lt (mulzN_le hlt z.isLt) redMax_lt, ?_⟩
  · simp only [opI, toW_val]
    generalize wb x = X at hx' ⊢
    generalize wb y = Y at hy' ⊢
    bv_omega
  · simp only [opI, toW_val]
    rw [bprod_toNat, hd, prodI]
  · rw [prodI, mulzN_mod hlt z.isLt, Nat.mul_comm]

theorem opI_bound (x y : Word) (z : Zq) {b : Nat} (hb : 1 ≤ b) (hb' : b ≤ 128) (hx : x.val < b * q)
    (hy : y.val < b * q) : (opI x y z).1.val < 2 * b * q ∧ (opI x y z).2.val < 2 * b * q := by
  have hv := opI_values x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb'))
    (Nat.lt_of_lt_of_le hy (Nat.mul_le_mul_right q hb'))
  rw [hv.1, hv.2.1, Nat.mul_assoc]
  constructor
  · omega_using [hx, hy]
  · exact Nat.lt_of_lt_of_le hv.2.2.1 (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left q hb))

theorem opI_residue (x y : Word) (z : Zq) (hx : x.val < 128 * q) (hy : y.val < 128 * q) :
    residue (opI x y z).1 = residue x + residue y ∧
    residue (opI x y z).2 = z * (residue x - residue y) := by
  have hv := opI_values x y z hx hy
  constructor
  · apply Fin.ext
    rw [Fin.val_add]
    change (opI x y z).1.val % q = (x.val % q + y.val % q) % q
    rw [hv.1, Nat.add_mod]
  · apply Fin.ext
    change (opI x y z).2.val % q = (z * (residue x - residue y)).val
    rw [hv.2.1, hv.2.2.2, Fin.val_mul, Fin.val_sub, residue, residue, Fin.val_ofNat, Fin.val_ofNat]
    have hl : (x.val + 128 * q - y.val) % q = (q - y.val % q + x.val % q) % q := by
      rw [q_eq] at hx hy ⊢; omega_using [hy]
    rw [Nat.mul_mod, hl, Nat.mul_mod z.val ((q - y.val % q + x.val % q) % q), Nat.mod_mod]

/-- The inverse butterfly with the negated zeta, as the code multiplies by
`negZetaTab`. -/
def opIn (x y : Word) (z : Zq) : Word × Word := opI x y (-z)

/-! ## Layers -/

/-- Words bounded by `b q` whose residues are `f`'s. -/
def Rel (b : Nat) (F : LPoly) (f : Poly) : Prop :=
  ∀ i < 256, F[i]!.val < b * q ∧ residue F[i]! = f[i]!

/-- A polynomial's coefficients as words. -/
def lift (f : Poly) : LPoly := f.map fun x => ⟨x.val, Nat.lt_trans (val_lt x) (by decide)⟩

theorem lift_get (f : Poly) {i : Nat} (hi : i < 256) : ((lift f)[i]!).val = (f[i]!).val := by
  rw [getElem!_pos (lift f) i hi, lift, Vector.getElem_map, getElem!_pos f i hi]

theorem lift_rel (f : Poly) : Rel 1 (lift f) f := by
  intro i hi
  have he := lift_get f hi
  refine ⟨by rw [he, Nat.one_mul]; exact f[i]!.isLt, Fin.ext ?_⟩
  rw [Fin.val_ofNat, he]; exact Nat.mod_eq_of_lt f[i]!.isLt

/-- The butterflies `op` of a block, with the zeta `Z k`, on words. -/
abbrev lblk (op : Word → Word → Zq → Word × Word) (Z : Nat → Zq) : LPoly → Nat → Nat → Nat → Nat → LPoly :=
  fun f len k st t => Lazy.blockN (Lazy.bfly op) f len (Z k) st t

/-- A layer of the forward butterflies on words. -/
def layerF (F : LPoly) (len : Nat) : LPoly :=
  Lazy.layF (lblk opF zetas) F len (fun c => 128 / len + c) (128 / len)

/-- A layer of the inverse butterflies on words. -/
def layerI (F : LPoly) (len : Nat) : LPoly :=
  Lazy.layF (lblk opI fun k => -zetas k) F len (fun c => 256 / len - 1 - c) (128 / len)

theorem lblkF_ok : Lazy.BlkOk (lblk opF zetas) opF := Lazy.block_ok opF

theorem lblkI_ok : Lazy.BlkOk (lblk opI fun k => -zetas k) opIn :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => Lazy.blockN_add _ _ _ _ _ _ _,
    fun f _ _ _ _ hl ht hs _ hi => Lazy.blockN_bfly_get' opI f hl ht hs hi⟩

/-- The facts of the layers' sizes. -/
theorem len_facts {len : Nat} (hlen : len ∈ nttLens) :
    0 < len ∧ 2 * len * (128 / len) = 256 ∧
      ∀ i < 256, (i % (2 * len) < len → i + len < 256) ∧ (¬ i % (2 * len) < len → len ≤ i) := by
  simp only [nttLens, List.mem_cons, List.not_mem_nil, or_false] at hlen
  rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨by decide, by decide, ?_⟩
  all_goals intro i hi; omega_using [hi]

theorem nttLayer_eq (F : Poly) (len : Nat) :
    nttLayer F len = layF (fun f len k st t => blockN VG.Proof.MlDsa.Arith.bfly f len (zetas k) st t) F len
      (fun c => 128 / len + c) (128 / len) := rfl

theorem nttInvLayer_eq (F : Poly) (len : Nat) :
    nttInvLayer F len = layF (fun f len k st t => blockN VG.Proof.MlDsa.Arith.bflyInv f len (-zetas k) st t)
      F len (fun c => 256 / len - 1 - c) (128 / len) := rfl

theorem layerF_rel {b : Nat} (hb : b ≤ 15) {F : LPoly} {f : Poly} (hF : Rel b F f)
    {len : Nat} (hlen : len ∈ nttLens) : Rel (b + 2) (layerF F len) (nttLayer f len) := by
  have hl := len_facts hlen
  intro i hi
  rw [layerF, Lazy.layF_get lblkF_ok F hl.1 _ (by omega) hi,
    nttLayer_eq, layF_get nttBlk_ok f hl.1 _ (by omega) hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    exact ⟨(opF_bound _ _ _ hb h0.1).1, by
      rw [(opF_residue _ _ _ (Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb))).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega_using [hi])
    have h1 := hF i hi
    exact ⟨(opF_bound _ _ _ hb h0.1).2, by
      rw [(opF_residue _ _ _ (Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb))).2, h0.2, h1.2]⟩

theorem layerI_rel {b : Nat} (hb : 1 ≤ b) (hb' : b ≤ 128) {F : LPoly} {f : Poly}
    (hF : Rel b F f) {len : Nat} (hlen : len ∈ nttLens) : Rel (2 * b) (layerI F len) (nttInvLayer f len) := by
  have hl := len_facts hlen
  have lt : ∀ {x : Word}, x.val < b * q → x.val < 128 * q := fun h =>
    Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right q hb')
  intro i hi
  rw [layerI, Lazy.layF_get lblkI_ok F hl.1 _ (by omega) hi,
    nttInvLayer_eq, layF_get nttInvBlk_ok f hl.1 _ (by omega) hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    exact ⟨(opI_bound _ _ (-_) hb hb' h0.1 h1.1).1, by
      rw [opIn, (opI_residue _ _ _ (lt h0.1) (lt h1.1)).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega_using [hi])
    have h1 := hF i hi
    refine ⟨(opI_bound _ _ (-_) hb hb' h0.1 h1.1).2, ?_⟩
    rw [opIn, (opI_residue _ _ _ (lt h0.1) (lt h1.1)).2, h0.2, h1.2]
    exact neg_mul_sub _ _ _

/-- The layers `ls` of `NTT`, from words less than `b q`. -/
theorem layersF_rel : ∀ (ls : List Nat) (b : Nat) (F : LPoly) (f : Poly), (∀ len ∈ ls, len ∈ nttLens) →
    b + 2 * ls.length ≤ 17 → Rel b F f → Rel (b + 2 * ls.length) (ls.foldl layerF F) (ls.foldl nttLayer f)
  | [], _, _, _, _, _, h => h
  | len :: ls, b, F, f, hls, hb, h => by
    rw [List.length_cons] at hb
    have := layersF_rel ls (b + 2) (layerF F len) (nttLayer f len) (fun l hl => hls l (List.mem_cons_of_mem _ hl))
      (by omega_using [hb]) (layerF_rel (by omega_using [hb]) h (hls len (List.mem_cons_self ..)))
    rw [List.length_cons, show b + 2 * (ls.length + 1) = b + 2 + 2 * ls.length by omega_arith]
    exact this

/-- The layers `ls` of `NTT⁻¹`, from words less than `b q`. -/
theorem layersI_rel : ∀ (ls : List Nat) (b : Nat) (F : LPoly) (f : Poly), (∀ len ∈ ls, len ∈ nttLens) →
    1 ≤ b → b * 2 ^ ls.length ≤ 256 → Rel b F f →
    Rel (b * 2 ^ ls.length) (ls.foldl layerI F) (ls.foldl nttInvLayer f)
  | [], b, _, _, _, _, _, h => by rw [List.length_nil, Nat.pow_zero, Nat.mul_one]; exact h
  | len :: ls, b, F, f, hls, hb1, hb, h => by
    rw [List.length_cons, Nat.pow_succ, Nat.mul_comm _ 2, ← Nat.mul_assoc, Nat.mul_comm b 2] at hb ⊢
    have h2 : 2 * b ≤ 256 := Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hb
    exact layersI_rel ls (2 * b) (layerI F len) (nttInvLayer f len)
      (fun l hl => hls l (List.mem_cons_of_mem _ hl)) (by omega_using [hb1]) hb
      (layerI_rel hb1 (by omega_using [h2]) h (hls len (List.mem_cons_self ..)))

/-! ## Words in memory -/

/-- The words of `W` stored at `p`. -/
def LP (m : Mem) (p : Addr) (W : LPoly) : Prop := ∀ i < n, (coeffAt m p i).toNat = W[i]!.val

/-- A stored polynomial, as words. -/
theorem lp_lift {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) : LP m p (lift f) := fun i hi => by
  rw [polyIs_toNat h hi, lift_get f (by rw [n_eq] at hi; exact hi)]

/-- A butterfly's two stores: `f[j + len]`, then `f[j]`. -/
theorem lp_bfly {m : Mem} {F : Addr} {W : LPoly} (h : LP m F W) (op : Word → Word → Zq → Word × Word)
    {j len : Nat} (hl : 0 < len) (hj : j + len < n) (z : Zq) {v₁ v₂ : BitVec 32}
    (h₁ : v₁.toNat = (op W[j]! W[j + len]! z).1.val) (h₂ : v₂.toNat = (op W[j]! W[j + len]! z).2.val) :
    LP ((m.writeW (coeffAddr F (j + len)) v₂).writeW (coeffAddr F j) v₁) F (Lazy.bfly op W j len z) := by
  intro i hi
  rw [coeffAt_writeW _ _ hi (by omega_using [hj]), coeffAt_writeW _ _ hi hj, Lazy.bfly_get op W hl hj z hi]
  rcases (by omega_using [] : i = j ∨ i = j + len ∨ (i ≠ j ∧ i ≠ j + len)) with rfl | rfl | ⟨a, b⟩
  · rw [ite_eq_left rfl, ite_eq_left rfl]; exact h₁
  · rw [ite_eq_right (by omega_using [hl]), ite_eq_left rfl, ite_eq_right (by omega_using [hl]), ite_eq_left rfl]
    exact h₂
  · rw [ite_eq_right (Ne.symm a), ite_eq_right (Ne.symm b), ite_eq_right a, ite_eq_right b]; exact h i hi

/-- An inverse butterfly's two stores: `f[j]`, then `f[j + len]`. -/
theorem lp_bflyInv {m : Mem} {F : Addr} {W : LPoly} (h : LP m F W) (op : Word → Word → Zq → Word × Word)
    {j len : Nat} (hl : 0 < len) (hj : j + len < n) (z : Zq) {v₁ v₂ : BitVec 32}
    (h₁ : v₁.toNat = (op W[j]! W[j + len]! z).1.val) (h₂ : v₂.toNat = (op W[j]! W[j + len]! z).2.val) :
    LP ((m.writeW (coeffAddr F j) v₁).writeW (coeffAddr F (j + len)) v₂) F (Lazy.bfly op W j len z) := by
  intro i hi
  rw [coeffAt_writeW _ _ hi hj, coeffAt_writeW _ _ hi (by omega_using [hj]), Lazy.bfly_get op W hl hj z hi]
  rcases (by omega_using [] : i = j ∨ i = j + len ∨ (i ≠ j ∧ i ≠ j + len)) with rfl | rfl | ⟨a, b⟩
  · rw [ite_eq_right (by omega_using [hl]), ite_eq_left rfl, ite_eq_left rfl]; exact h₁
  · rw [ite_eq_left rfl, ite_eq_right (by omega_using [hl]), ite_eq_left rfl]; exact h₂
  · rw [ite_eq_right (Ne.symm b), ite_eq_right (Ne.symm a), ite_eq_right a, ite_eq_right b]; exact h i hi

/-! ## Butterflies -/

/-- `-q`, the constant `k5`, and the zeta `z` with its `zp`, in `r4`–`r7`. -/
def ZetaIn (k5 : BitVec 32) (z : Zq) (s : State) : Prop :=
  s.gpr .r4 = Nw ∧ s.gpr .r5 = k5 ∧ s.gpr .r6 = zb z ∧ s.gpr .r7 = bquot (zb z)

/-- The registers the loops of the transforms keep. -/
abbrev bflyKeep : List Reg := [.r1, .r2, .r4, .r5, .r6, .r7, .r11, .lr]

/-- The code `code len` stores what the butterfly `op` gives of the words
`j` and `j + len` of the polynomial at `p`, with `r0` pointing at
coefficient `j`, the zeta in `r6` and `r7`, `k5` in `r5`, and `r3` counting
down. -/
def BflyOk (code : Nat → List Instr) (op : Word → Word → Zq → Word × Word) (k5 : BitVec 32) : Prop :=
  ∀ (p : BitVec 32) (len j : Nat), 0 < len → len ≤ 128 → j + len < 256 → p.toNat + 1024 ≤ 2 ^ 32 →
    ∀ (z : Zq) (G : LPoly) (s : State), s.gpr .r0 = p + BitVec.ofNat 32 (4 * j) → ZetaIn k5 z s →
      LP s.mem (State.addr p) G → polyRegion (State.addr p) ∈ s.wr →
      WP isa (.block (code len)) s fun s' =>
        LP s'.mem (State.addr p) (Lazy.bfly op G j len z) ∧ Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (j + 1)) ∧ s'.gpr .r3 = s.gpr .r3 - 1 ∧
        s'.z = (s.gpr .r3 - 1 == 0) ∧ Keep bflyKeep s s'

/-! ## Loads, stores and values -/

/-- A pointer to coefficient `j`, plus the offset of coefficient `j + k`. -/
theorem addr_at {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {j k : Nat} (h : j + k < 256) :
    State.addr (p + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 (4 * k)) = coeffAddr (State.addr p) (j + k) := by
  rw [addr_ptr _ _ _ (by omega_using [hp, h]), ← Nat.mul_add]

theorem addr_at0 {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {j : Nat} (h : j < 256) :
    State.addr (p + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 0) = coeffAddr (State.addr p) j :=
  addr_at (k := 0) hp h

theorem wr_at {p : BitVec 32} {s : State} (hw : polyRegion (State.addr p) ∈ s.wr) {j : Nat} (h : j < 256) :
    InRegions s.wr (coeffAddr (State.addr p) j) 4 :=
  inRegions_of hw (coeff_contains _ h)

theorem rd_at {p : BitVec 32} {s : State} (hw : polyRegion (State.addr p) ∈ s.wr) {j : Nat} (h : j < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (State.addr p) j) 4 :=
  inRegions_of (List.mem_append_right _ hw) (coeff_contains _ h)

theorem ptr_next (p : BitVec 32) (j : Nat) :
    p + BitVec.ofNat 32 (4 * j) + 4 = p + BitVec.ofNat 32 (4 * (j + 1)) := by
  rw [BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add, Nat.mul_succ]

/-- The word stored for a coefficient. -/
theorem word_val {m : Mem} {P : Addr} {G : LPoly} (h : LP m P G) {j : Nat} (hj : j < 256) :
    m.readW (coeffAddr P j) 32 = wb G[j]! := by
  rw [← coeffAt_eq]; exact wb_of (h j hj)

/-! ## `NTT` -/

/-- The butterfly of `NTT` after the load and `mulz`. -/
def bflyRest (len : Nat) : List Instr :=
  [.ldr .r8 .r0 0, .dp .add .r12 .r8 (.reg .r10), .dp .add .r8 .r8 (.reg .r5), .dp .sub .r8 .r8 (.reg .r10),
    .str .r8 .r0 (4 * len), .str .r12 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]

theorem bfly_split (len : Nat) :
    Impl.MlDsa.Arm.Arith.bfly len = ([.ldr .r9 .r0 (4 * len)] : List Instr) ++ (mulz .r10 .r9 .r12 ++ bflyRest len) := by
  simp only [Impl.MlDsa.Arm.Arith.bfly, bflyRest, List.append_assoc]

section
variable {s : State} {x c k5 v : BitVec 32} {len : Nat} (hlen : 4 * len < 4096) (h0 : s.gpr .r0 = x)
  (h3 : s.gpr .r3 = c) (h5 : s.gpr .r5 = k5) (h10 : s.gpr .r10 = v)
  (iA : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
  (oB : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * len))) 4)
include hlen h0 h3 h5 h10 iA oA oB

theorem bflyRest_ok :
    WP isa (.block (bflyRest len)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * len)))
          (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 + k5 - v)).writeW
        (State.addr (x + BitVec.ofNat 32 0)) (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 + v) ∧
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ Keep bflyKeep s s' := by
  run_block [bflyRest, Keep, h0, h3, h5, h10, iA, oA, oB, hlen, List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> rfl

end

theorem bfly_spec : BflyOk Impl.MlDsa.Arm.Arith.bfly opF 16760834 := by
  intro p len j hl hl' hj hp z G s h0 hz hG hw
  obtain ⟨z4, z5, z6, z7⟩ := hz
  have eB := addr_at hp hj (j := j) (k := len)
  have eA := addr_at0 hp (j := j) (by omega_using [hj])
  rw [bfly_split, WP.block_append_iff]
  have iB : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * len))) 4 := by
    rw [h0, eB]; exact rd_at hw hj
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_ldr (by omega_using [hl']) iB, runStep_some, runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (mulz_ok (s := s.setReg .r9 _) (b := s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * len))) 32)
    (z := zb z) (zp := bquot (zb z)) (by simp [State.setReg, z4]) (by simp [State.setReg, z6])
    (by simp [State.setReg, z7]) (by simp [State.setReg]))
    fun s₁ ⟨e10, eo, m₁, rd₁, wr₁, sp₁⟩ => ?_
  have g : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s₁.gpr r = s.gpr r := fun r a9 a10 a12 => by
    rw [eo r a9 a10 a12]; simp [State.setReg, a9]
  have hw₁ : polyRegion (State.addr p) ∈ s₁.wr := by rw [wr₁]; exact hw
  refine WP.mono (bflyRest_ok (s := s₁) (x := p + BitVec.ofNat 32 (4 * j)) (by omega_using [hl'])
    ((g _ (by decide) (by decide) (by decide)).trans h0) rfl ((g _ (by decide) (by decide) (by decide)).trans z5)
    e10 (by rw [eA]; exact rd_at hw₁ (by omega_using [hj])) (by rw [eA]; exact wr_at hw₁ (by omega_using [hj]))
    (by rw [eB]; exact wr_at hw₁ hj)) fun s' ⟨hm, r0, r3, hzf, hk⟩ => ?_
  have nk : ∀ r ∈ bflyKeep, r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r12 := by decide
  have k₁ : Keep bflyKeep s s₁ := ⟨fun r hr => g r (nk r hr).1 (nk r hr).2.1 (nk r hr).2.2, rd₁, wr₁, sp₁⟩
  have e3 : s₁.gpr .r3 = s.gpr .r3 := g _ (by decide) (by decide) (by decide)
  have hjn : j < n := by rw [n_eq]; omega_using [hj]
  have hjl : j + len < n := by rw [n_eq]; omega_using [hj]
  refine ⟨?_, ?_, by rw [r0]; exact ptr_next p j, by rw [r3, e3], by rw [hzf, e3], k₁.trans hk⟩
  · rw [hm, m₁, eA, eB]
    simp only [State.setReg]
    rw [h0, eB, word_val hG hj, word_val hG (by omega_using [hj])]
    exact lp_bfly hG opF hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, m₁, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hj)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjn)

/-! ## `NTT⁻¹` -/

/-- The butterfly of `NTT⁻¹` before `mulz`. -/
def bflyInvPre (len : Nat) : List Instr :=
  [.ldr .r8 .r0 0, .ldr .r9 .r0 (4 * len), .dp .add .r12 .r8 (.reg .r9), .str .r12 .r0 0,
    .dp .add .r8 .r8 (.reg .r5), .dp .sub .r9 .r8 (.reg .r9)]

/-- The butterfly of `NTT⁻¹` after `mulz`. -/
def bflyInvPost (len : Nat) : List Instr :=
  [.str .r10 .r0 (4 * len), .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]

theorem bflyInv_split (len : Nat) :
    Impl.MlDsa.Arm.Arith.bflyInv len = bflyInvPre len ++ (mulz .r10 .r9 .r12 ++ bflyInvPost len) := by
  simp only [Impl.MlDsa.Arm.Arith.bflyInv, bflyInvPre, bflyInvPost, List.append_assoc]

section
variable {s : State} {x k5 : BitVec 32} {len : Nat} (hlen : 4 * len < 4096) (h0 : s.gpr .r0 = x)
  (h5 : s.gpr .r5 = k5)
  (iA : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (iB : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * len))) 4)
  (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include hlen h0 h5 iA iB oA

theorem bflyInvPre_ok :
    WP isa (.block (bflyInvPre len)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0))
        (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 +
          s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * len))) 32) ∧
      s'.gpr .r9 = s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 + k5 -
          s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * len))) 32 ∧
      s'.gpr .r0 = x ∧ s'.gpr .r3 = s.gpr .r3 ∧ Keep bflyKeep s s' := by
  run_block [bflyInvPre, h0, h5, iA, iB, oA, hlen]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> rfl

end

section
variable {s : State} {x c v : BitVec 32} {len : Nat} (hlen : 4 * len < 4096) (h0 : s.gpr .r0 = x)
  (h3 : s.gpr .r3 = c) (h10 : s.gpr .r10 = v)
  (oB : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * len))) 4)
include hlen h0 h3 h10 oB

theorem bflyInvPost_ok :
    WP isa (.block (bflyInvPost len)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * len))) v ∧
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ Keep bflyKeep s s' := by
  run_block [bflyInvPost, h0, h3, h10, oB, hlen]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> rfl

end

theorem bflyInv_spec : BflyOk Impl.MlDsa.Arm.Arith.bflyInv opI 1072693376 := by
  intro p len j hl hl' hj hp z G s h0 hz hG hw
  obtain ⟨z4, z5, z6, z7⟩ := hz
  have eB := addr_at hp hj (j := j) (k := len)
  have eA := addr_at0 hp (j := j) (by omega_using [hj])
  have hjn : j < n := by rw [n_eq]; omega_using [hj]
  have hjl : j + len < n := by rw [n_eq]; omega_using [hj]
  rw [bflyInv_split, WP.block_append_iff]
  refine WP.mono (bflyInvPre_ok (len := len) (by omega_using [hl']) h0 z5 (by rw [eA]; exact rd_at hw hjn)
    (by rw [eB]; exact rd_at hw hj) (by rw [eA]; exact wr_at hw hjn)) fun s₁ ⟨m₁, e9, e0, e3, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulz_ok (k₁.gpr .r4 (by decide) ▸ z4) (k₁.gpr .r6 (by decide) ▸ z6)
    (k₁.gpr .r7 (by decide) ▸ z7) e9)
    fun s₂ ⟨e10, eo, m₂, rd₂, wr₂, sp₂⟩ => ?_
  have nk : ∀ r ∈ bflyKeep, r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r12 := by decide
  have k₂ : Keep bflyKeep s₁ s₂ := ⟨fun r hr => eo r (nk r hr).1 (nk r hr).2.1 (nk r hr).2.2, rd₂, wr₂, sp₂⟩
  have hw₂ : polyRegion (State.addr p) ∈ s₂.wr := by rw [k₂.wr, k₁.wr]; exact hw
  refine WP.mono (bflyInvPost_ok (s := s₂) (x := p + BitVec.ofNat 32 (4 * j)) (len := len) (by omega_using [hl'])
    ((eo _ (by decide) (by decide) (by decide)).trans e0) rfl e10
    (by rw [eB]; exact wr_at hw₂ hj)) fun s' ⟨hm, r0, r3, hzf, k₃⟩ => ?_
  have e3' : s₂.gpr .r3 = s.gpr .r3 := (eo _ (by decide) (by decide) (by decide)).trans e3
  refine ⟨?_, ?_, by rw [r0]; exact ptr_next p j, by rw [r3, e3'], by rw [hzf, e3'], (k₁.trans k₂).trans k₃⟩
  · rw [hm, m₂, m₁, eA, eB, word_val hG hjn, word_val hG hj]
    exact lp_bflyInv hG opI hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, m₂, m₁, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjn)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hj)

end VG.Proof.MlDsa.Arm.Arith

end

end


/-!
# ML-DSA on 32-bit ARM: the table, blocks and layers of `NTT` and `NTT⁻¹`

`storeTab t 256` leaves the `u32`s `t 0, …, t 255` at `r1` (`Tab`,
`storeTab_ok`). The loops of `nttBlk` and `nttLay`, for any butterfly code
that does what a butterfly `op` of the specification does (`BflyOk`): a block
runs `len` butterflies (`Lazy.blockN`), and a layer its `128 / len` blocks
(`Lazy.layF`), on words, with the zetas `Z (zi c)`, whose values `tab` the
table at `zB` holds.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Arith

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)

/-! ## The table -/

/-- The `u32`s at `P` are the table `t`. -/
def Tab (t : Nat → Nat) (m : Mem) (P : Addr) : Prop := ∀ k < 256, coeffAt m P k = BitVec.ofNat 32 (t k)

/-- The table `tab` holds the values of the zetas `Z`. -/
def TabOf (tab : Nat → Nat) (Z : Nat → Zq) : Prop := ∀ k < 256, tab k = (Z k).val

theorem tab_word {t : Nat → Nat} (ht : ∀ k < 256, t k < q) (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 (t i / 65536) ++ ((BitVec.ofNat 16 (t i % 65536)).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 (t i) := by
  have := ht i hi
  rw [q_eq] at this
  generalize t i = v at *
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_zero, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega_using [])]
  omega_using []

theorem tabStep_ok (t : Nat → Nat) (ht : ∀ k < 256, t k < q) {i : Nat} (hi : i < 256) (s : State) {zB : BitVec 32}
    (h1 : s.gpr .r1 = zB) (hw : InRegions s.wr (State.addr (zB + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block (tabStep t i)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (zB + BitVec.ofNat 32 (4 * i))) (BitVec.ofNat 32 (t i)) ∧
        Keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' := by
  have ho : 4 * i < 4096 := by omega_using [hi]
  run_block [tabStep, h1, hw, ho, tab_word ht i hi]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl

/-- The table, stored in the 1024 bytes at `r1`. -/
theorem storeTab_ok (t : Nat → Nat) (ht : ∀ k < 256, t k < q) (s : State) {zB : BitVec 32}
    (h1 : s.gpr .r1 = zB) (hfit : zB.toNat + 1024 ≤ 2 ^ 32) (hw : polyRegion (State.addr zB) ∈ s.wr) :
    WP isa (.block (storeTab t 256)) s fun s' =>
      Tab t s'.mem (State.addr zB) ∧ Frame [polyRegion (State.addr zB)] s.mem s'.mem ∧
        Keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9,
      .r10, .r11, .lr] s s' ∧ Frame [polyRegion (State.addr zB)] s.mem s'.mem ∧
      ∀ j < k, coeffAt s'.mem (State.addr zB) j = BitVec.ofNat 32 (t j))
    (fun k s' hk ⟨hk', hf, ht'⟩ => ?_) 256 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s' ⟨hk, hf, ht'⟩ => ⟨ht', hf, hk⟩
  have e : State.addr (zB + BitVec.ofNat 32 (4 * k)) = coeffAddr (State.addr zB) k := by
    have := addr_ptr zB (4 * k) 0 (by omega_using [hfit, hk])
    simp only [Nat.add_zero, BitVec.add_zero] at this
    exact this
  have hk256 : k < n := by rw [n_eq]; exact hk
  refine WP.mono (tabStep_ok t ht hk s' ((hk'.gpr .r1 (by decide)).trans h1)
      (by rw [e, hk'.wr]; exact inRegions_of hw (coeff_contains _ hk256)))
    fun s'' ⟨hm', hk''⟩ => ⟨hk'.trans hk'', ?_, fun j hj => ?_⟩
  · rw [hm', e]
    exact hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk256)
  · rw [hm', e, coeffAt_writeW _ _ (show j < n by rw [n_eq]; omega_using [hk, hj]) hk256]
    by_cases e' : k = j
    · subst e'; rw [ite_eq_left rfl]
    · rw [ite_eq_right e']; exact ht' j (by omega_using [hj, e'])

/-- Writes elsewhere keep the table. -/
theorem Tab.frame {t : Nat → Nat} {m m' : Mem} {P : Addr} (h : Tab t m P) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (polyRegion P).Disjoint r) : Tab t m' P :=
  fun k hk => by rw [coeffAt_frame hf hd (show k < n by rw [n_eq]; exact hk)]; exact h k hk

/-! ## A block -/

section
variable {code : Nat → List Instr} {op : Word → Word → Zq → Word × Word} {k5 : BitVec 32}
  (hb : BflyOk code op k5)
include hb

/-- The `len` butterflies of a block. -/
theorem bflys_ok {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {len start : Nat} (hlen : 0 < len)
    (hl : len ≤ 128) (hs : start + 2 * len ≤ 256) (z : Zq) (G : LPoly) (s : State)
    (h0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * start)) (hz : ZetaIn k5 z s) (hG : LP s.mem (State.addr p) G)
    (hw : polyRegion (State.addr p) ∈ s.wr) (h3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (len - 0))) :
    WP isa (.loop (.block (code len)) .ne) s fun s' =>
      LP s'.mem (State.addr p) (Lazy.blockN (Lazy.bfly op) G len z start len) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + len)) ∧ Keep bflyKeep s s' := by
  refine wp_loop_ne (fun t s' => LP s'.mem (State.addr p) (Lazy.blockN (Lazy.bfly op) G len z start t) ∧
      Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + t)) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (1 * (len - t)) ∧ Keep bflyKeep s s') hlen
    (fun t ht s' ⟨hP, hf, h0', h3', hk⟩ => ?_) (fun _ ⟨hP, hf, h0', _, hk⟩ => ⟨hP, hf, h0', hk⟩)
    ⟨hG, Frame.refl _ _, by rw [h0, Nat.add_zero], h3, Keep.refl _ _⟩
  obtain ⟨z4, z5, z6, z7⟩ := hz
  have hz' : ZetaIn k5 z s' := ⟨(hk.gpr .r4 (by decide)).trans z4, (hk.gpr .r5 (by decide)).trans z5,
    (hk.gpr .r6 (by decide)).trans z6, (hk.gpr .r7 (by decide)).trans z7⟩
  refine WP.mono (hb p len (start + t) hlen hl (by omega_using [hs, ht]) hp z _ s' h0' hz' hP (by rw [hk.wr]; exact hw))
    fun s'' ⟨hP', hf', h0'', h3'', hz'', hk'⟩ => ⟨⟨?_, hf.trans hf', ?_, ?_, hk.trans hk'⟩, ?_⟩
  · rw [Lazy.blockN_succ]; exact hP'
  · rw [h0'', Nat.add_assoc]
  · rw [h3'', h3']; exact count_sub (k := 1) ht
  · rw [hz'', h3']; exact count_z (k := 1) ht (by decide) (by omega_using [hl])

omit hb in
theorem blkPre_ok (len : Nat) (hl : len ≤ 128) (op : DpOp) (hop : op = .add ∨ op = .sub) (s : State)
    {x : BitVec 32} (h1 : s.gpr .r1 = x) (hi : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block (([.ldr .r6 .r1 0] : List Instr) ++ quot .r7 .r6 ++
      ([.dp op .r1 .r1 (.imm 4), .mov .r3 (.imm (BitVec.ofNat 32 len))] : List Instr))) s fun s' =>
      s'.gpr .r6 = s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 ∧
      s'.gpr .r7 = bquot (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32) ∧
      s'.gpr .r1 = (if op = .add then x + 4 else x - 4) ∧ s'.gpr .r3 = BitVec.ofNat 32 len ∧
      s'.mem = s.mem ∧ Keep [.r0, .r2, .r4, .r5, .r11, .lr] s s' := by
  have he : encodable (BitVec.ofNat 32 len) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 l) = true := by decide
    exact this len (by omega_using [hl])
  rcases hop with rfl | rfl <;>
  · run_block [quot, bquot, h1, hi, he]
    keep_simp

omit hb in
theorem blkPost_ok (len : Nat) (hl : len ≤ 128) (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4 * len))), .subs .r2 .r2 (.imm 1)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 (4 * len) ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧
        s'.z = (s.gpr .r2 - 1 == 0) ∧ s'.mem = s.mem ∧ Keep [.r1, .r4, .r5, .r6, .r7, .r11, .lr] s s' := by
  have he : encodable (BitVec.ofNat 32 (4 * len)) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 (4 * l)) = true := by decide
    exact this len (by omega_using [hl])
  run_block [he]
  keep_simp

/-- The pointer to the next zeta. -/
def nextZ (op : DpOp) (x : BitVec 32) : BitVec 32 := if op = .add then x + 4 else x - 4

/-- A block, with the zeta `Z k` at `r1`. -/
theorem blk_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : TabOf tab Z) {p zB : BitVec 32}
    (hp : p.toNat + 1024 ≤ 2 ^ 32) (hzf : zB.toNat + 1024 ≤ 2 ^ 32) {len start k : Nat}
    (hlen : 0 < len) (hl : len ≤ 128) (hs : start + 2 * len ≤ 256) (hk : k < 256) (dop : DpOp)
    (hop : dop = .add ∨ dop = .sub) (G : LPoly) (s : State) (h0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * start))
    (h1 : s.gpr .r1 = zB + BitVec.ofNat 32 (4 * k)) (h4 : s.gpr .r4 = Nw) (h5 : s.gpr .r5 = k5)
    (hG : LP s.mem (State.addr p) G)
    (hw : polyRegion (State.addr p) ∈ s.wr) (hzw : polyRegion (State.addr zB) ∈ s.rd ++ s.wr)
    (ht : Tab tab s.mem (State.addr zB)) :
    WP isa (nttBlk (code len) len dop) s fun s' =>
      LP s'.mem (State.addr p) (lblk op Z G len k start len) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + 2 * len)) ∧ s'.gpr .r1 = nextZ dop (s.gpr .r1) ∧
        s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧ Keep [.r4, .r5, .r11, .lr] s s' := by
  have eZ : State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) = coeffAddr (State.addr zB) k :=
    addr_at0 hzf hk
  refine WP.seq (WP.mono (blkPre_ok len hl dop hop s h1 (by
    rw [eZ]; exact inRegions_of hzw (coeff_contains _ (show k < n by rw [n_eq]; exact hk))))
    fun s₁ ⟨e6, e7, e1, e3, m₁, k₁⟩ => ?_)
  have hwv : s.mem.readW (State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 32 = zb (Z k) := by
    rw [eZ, ← coeffAt_eq, ht k hk, hZ k hk]
  rw [hwv] at e6 e7
  refine WP.seq (WP.mono (bflys_ok hb hp hlen hl hs (Z k) G s₁ ((k₁.gpr .r0 (by decide)).trans h0)
    ⟨(k₁.gpr .r4 (by decide)).trans h4, (k₁.gpr .r5 (by decide)).trans h5, e6, e7⟩ (by rw [m₁]; exact hG)
    (by rw [k₁.wr]; exact hw) (by rw [e3]; simp)) fun s₂ ⟨hP, hf, h0₂, k₂⟩ => ?_)
  refine WP.mono (blkPost_ok len hl s₂) fun s' ⟨h0', h2', hz', m', k₃⟩ => ⟨by rw [m']; exact hP,
    by rw [m', ← m₁]; exact hf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0', h0₂, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_using []
  · rw [k₃.gpr .r1 (by decide), k₂.gpr .r1 (by decide), e1, h1]; rfl
  · rw [h2', k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · rw [hz', k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · exact ((k₁.mono (rs' := [.r4, .r5, .r11, .lr]) (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))

omit hb in
theorem layPre_ok (c : Nat) (hc : c ≤ 128) (s : State) :
    WP isa (.block [.mov .r2 (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      s'.gpr .r2 = BitVec.ofNat 32 c ∧ s'.mem = s.mem ∧ Keep [.r0, .r1, .r4, .r5, .r11, .lr] s s' := by
  have he : encodable (BitVec.ofNat 32 c) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 l) = true := by decide
    exact this c (by omega_using [hc])
  run_block [he]
  keep_simp

omit hb in
theorem layPost_ok (s : State) :
    WP isa (.block [.dp .sub .r0 .r0 (.imm 1024)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 - 1024 ∧ s'.mem = s.mem ∧ Keep [.r1, .r4, .r5, .r11, .lr] s s' := by
  run_block []
  keep_simp

omit hb in
/-- The facts about the lengths of the layers. -/
theorem lens_facts : ∀ len ∈ nttLens, 0 < len ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
    128 / len ≤ 128 := by
  decide

/-- A layer, from `r0` = `f` and the zeta of its first block at `r1`. -/
theorem lay_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : TabOf tab Z) {p zB : BitVec 32}
    (hp : p.toNat + 1024 ≤ 2 ^ 32) (hzf : zB.toNat + 1024 ≤ 2 ^ 32) {len : Nat} (hlen : len ∈ nttLens)
    (dop : DpOp) (hop : dop = .add ∨ dop = .sub) (zi : Nat → Nat) (hzi : ∀ c < 128 / len, zi c < 256)
    (hstep : ∀ c < 128 / len, nextZ dop (zB + BitVec.ofNat 32 (4 * zi c)) = zB + BitVec.ofNat 32 (4 * zi (c + 1)))
    (F : LPoly) (s : State) (h0 : s.gpr .r0 = p) (h1 : s.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi 0))
    (h4 : s.gpr .r4 = Nw) (h5 : s.gpr .r5 = k5) (hF : LP s.mem (State.addr p) F)
    (hw : polyRegion (State.addr p) ∈ s.wr)
    (hzw : polyRegion (State.addr zB) ∈ s.rd ++ s.wr)
    (hd : (polyRegion (State.addr zB)).Disjoint (polyRegion (State.addr p))) (ht : Tab tab s.mem (State.addr zB)) :
    WP isa (nttLay (code len) len dop) s fun s' =>
      LP s'.mem (State.addr p) (Lazy.layF (lblk op Z) F len zi (128 / len)) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p ∧
        s'.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi (128 / len)) ∧ Keep [.r4, .r5, .r11, .lr] s s' := by
  obtain ⟨hl0, hl1, hl2, hl3, hl4⟩ := lens_facts len hlen
  have hdd : ∀ r ∈ [polyRegion (State.addr p)], (polyRegion (State.addr zB)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hd
  refine WP.seq (WP.mono (layPre_ok (128 / len) hl4 s) fun s₁ ⟨e2, m₁, k₁⟩ => WP.seq ?_)
  refine WP.mono (Q := fun (s₂ : State) => LP s₂.mem (State.addr p) (Lazy.layF (lblk op Z) F len zi (128 / len)) ∧
      Frame [polyRegion (State.addr p)] s.mem s₂.mem ∧ s₂.gpr .r0 = p + BitVec.ofNat 32 (4 * 256) ∧
      s₂.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi (128 / len)) ∧ Keep [.r4, .r5, .r11, .lr] s s₂) ?_
    fun s₂ ⟨hP, hf, h0₂, h1₂, k₂⟩ => ?_
  · refine wp_loop_ne (fun c s' => LP s'.mem (State.addr p) (Lazy.layF (lblk op Z) F len zi c) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (2 * len * c)) ∧
        s'.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi c) ∧ s'.gpr .r2 = BitVec.ofNat 32 (1 * (128 / len - c)) ∧
        Keep [.r4, .r5, .r11, .lr] s s') hl3 (fun c hc s' ⟨hP, hf, h0', h1', h2', hk⟩ => ?_)
      (fun s' ⟨hP, hf, h0', h1', _, hk⟩ => ⟨hP, hf, by rw [h0', hl2], h1', hk⟩)
      ⟨by rw [m₁]; exact hF, by rw [m₁]; exact Frame.refl _ _, by rw [k₁.gpr .r0 (by decide), h0]; simp,
        by rw [k₁.gpr .r1 (by decide), h1], by rw [e2]; simp, k₁.mono (by decide)⟩
    have hcm : 2 * len * c + 2 * len ≤ 256 := by
      have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega_using [hc])
      rw [Nat.mul_succ] at this; omega_using [hl2, this]
    refine WP.mono (blk_ok hb hZ hp hzf hl0 hl1 hcm (hzi c hc) dop hop _ s' h0' h1'
      ((hk.gpr .r4 (by decide)).trans h4) ((hk.gpr .r5 (by decide)).trans h5) hP (by rw [hk.wr]; exact hw)
      (by rw [hk.rd, hk.wr]; exact hzw)
      (ht.frame hf hdd)) fun s'' ⟨hP', hf', h0'', h1'', h2'', hz'', hk'⟩ => ⟨⟨?_, hf.trans hf', ?_, ?_, ?_,
        hk.trans hk'⟩, ?_⟩
    · rw [Lazy.layF, foldl_range_succ, ← Lazy.layF]; exact hP'
    · rw [h0'', Nat.mul_succ]
    · rw [h1'', h1', hstep c hc]
    · rw [h2'', h2']; exact count_sub (k := 1) hc
    · rw [hz'', h2']; exact count_z (k := 1) hc (by decide) (by omega_using [hl4])
  · refine WP.mono (layPost_ok s₂) fun s' ⟨h0', m', k₃⟩ => ⟨by rw [m']; exact hP, by rw [m']; exact hf, ?_,
      by rw [k₃.gpr .r1 (by decide), h1₂], k₂.trans (k₃.mono (by decide))⟩
    rw [h0', h0₂]
    exact BitVec.add_sub_cancel _ _

end

/-! ## A loop over the coefficients -/

/-- The code `body` replaces the coefficient at `r0` by `g` of it, moves `r0`
to the next, and counts down in `r3`, keeping what `C` says of the
registers. -/
def MapOk (body : List Instr) (g : BitVec 32 → BitVec 32) (C : State → Prop) : Prop :=
  ∀ (s : State) (x c : BitVec 32), s.gpr .r0 = x → s.gpr .r3 = c → C s →
    InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
    InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4 →
    WP isa (.block body) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0))
        (g (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)) ∧
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ C s' ∧ Keep [.r11, .lr] s s'

/-- The loop of such a body over the 256 coefficients of the polynomial at
`p`. -/
theorem map_ok {body : List Instr} {g : BitVec 32 → BitVec 32} {C : State → Prop} (hb : MapOk body g C)
    {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {s : State} (hw : polyRegion (State.addr p) ∈ s.wr)
    (h0 : s.gpr .r0 = p) (h3 : s.gpr .r3 = BitVec.ofNat 32 256) (hC : C s) :
    WP isa (.loop (.block body) .ne) s fun s' =>
      (∀ j < 256, coeffAt s'.mem (State.addr p) j = g (coeffAt s.mem (State.addr p) j)) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ Keep [.r11, .lr] s s' := by
  refine wp_loop_ne (fun t s' => s'.gpr .r0 = p + BitVec.ofNat 32 (4 * t) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (1 * (256 - t)) ∧ C s' ∧ Keep [.r11, .lr] s s' ∧
      Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
      ∀ j < 256, coeffAt s'.mem (State.addr p) j =
        if j < t then g (coeffAt s.mem (State.addr p) j) else coeffAt s.mem (State.addr p) j) (N := 256) (by decide)
    (fun t ht s' ⟨r0, r3, hC', hk, hf, hc⟩ => ?_)
    (fun s' ⟨_, _, _, hk, hf, hc⟩ => ⟨fun j hj => by rw [hc j hj, ite_eq_left hj], hf, hk⟩)
    ⟨by rw [h0]; simp, h3, hC, Keep.refl _ _, Frame.refl _ _, fun j _ => by rw [ite_eq_right (Nat.not_lt_zero j)]⟩
  have htn : t < n := by rw [n_eq]; exact ht
  have eA := addr_at0 hp ht
  have hw' : polyRegion (State.addr p) ∈ s'.wr := by rw [hk.wr]; exact hw
  refine WP.mono (hb s' _ _ r0 r3 hC' (by rw [eA]; exact rd_at hw' htn) (by rw [eA]; exact wr_at hw' htn))
    fun s'' ⟨hm, r0', r3', hz, hC'', hk'⟩ => ⟨⟨?_, ?_, hC'', hk.trans hk', ?_, fun j hj => ?_⟩, ?_⟩
  · rw [r0']; exact ptr_next p t
  · rw [r3']; exact count_sub (k := 1) ht
  · rw [hm, eA]; exact hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ htn)
  · rw [hm, eA, ← coeffAt_eq, coeffAt_writeW _ _ (show j < n by rw [n_eq]; exact hj) htn, hc j hj,
      hc t ht, ite_eq_right (Nat.lt_irrefl t)]
    by_cases e : t = j
    · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self t)]
    · rw [ite_eq_right e]
      by_cases hj' : j < t
      · rw [ite_eq_left hj', ite_eq_left (by omega_using [hj'])]
      · rw [ite_eq_right hj', ite_eq_right (by omega_using [e, hj'])]
  · rw [hz]; exact count_z (k := 1) ht (by decide) (by decide)

/-- A word reduced is its residue. -/
theorem canon_val {v : BitVec 32} {x : Word} (hv : v.toNat = x.val) : (bcsub (bred v)).toNat = (residue x).val := by
  have hr := red23_le (x := v.toNat) v.isLt
  rw [bcsub_toNat (by rw [bred_toNat]; exact Nat.lt_of_le_of_lt hr redMax_lt), bred_toNat, red23_mod, hv,
    Fin.val_ofNat]

/-- A word times a zeta, reduced, is the product of its residue and the zeta. -/
theorem scale_val {v : BitVec 32} {x : Word} (hv : v.toNat = x.val) (z : Zq) :
    (bcsub (bprod v z)).toNat = (residue x * z).val := by
  have hr := mulzN_le (b := v.toNat) v.isLt z.isLt
  rw [bcsub_toNat (by rw [bprod_toNat]; exact Nat.lt_of_le_of_lt hr redMax_lt), bprod_toNat,
    mulzN_mod v.isLt z.isLt, hv, Fin.val_mul, Fin.val_ofNat, Nat.mod_mul_mod]

end VG.Proof.MlDsa.Arm.Arith
