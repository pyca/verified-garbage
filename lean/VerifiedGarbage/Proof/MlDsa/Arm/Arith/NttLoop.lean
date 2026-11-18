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
to `mulzV u`'s value (`bprod u`: `mulz`'s or, with `umaal`, `mulzU`'s, each
less than `2q` and congruent to the product, `bprod_lt` and `bprod_mod`, which
is all the layers below use of it), and store the sum and
the difference as they are: the coefficients between layers are words
(`Proof/MlDsa/Arith/Lazy.lean`'s `Word`) congruent to the specification's,
and bounded by a multiple of `q` that grows with each layer, as on RISC-V
(`Proof/MlDsa/RISCV64/Arith/Lazy.lean`).

* `opF` is what the forward butterfly stores, `(x + t, x + 2q - t)` for the
  reduced product `t` of `y` and the zeta, on 32 bits, so that the stores
  are `opF` for every input; for `x < 15q` it is that sum and difference
  (`opF_values`), less than `2q` more than `x` and congruent to the
  specification's butterfly (`opF_bound`, `opF_residue`). A layer then takes
  `Rel b` to `Rel (b + 2)` (`layerF_rel`): seven layers from `Rel 1` end at
  `Rel 15`.
* `opI` is the inverse butterfly's, `(x + y, t)` for the reduced product `t`
  of the zeta and `x + 128q - y`: for `x, y < b q` with `b ≤ 128`, that sum
  and a product below `2q` (`opI_values`), so a layer takes `Rel b` to
  `Rel 2b` (`layerI_rel`), and seven layers from `Rel 1` end at `Rel 128`,
  every coefficient less than `128 q < 2³⁰`.

The last layer of each transform stores canonical coefficients. `NTT`'s
stores `opFC`, `opF` reduced (`canon_val`), so that the layer leaves the
specification's coefficients from words below `15 q` (`layerFC_val`).
`NTT⁻¹`'s stores `opIS`, the sum times `256⁻¹` and the difference times the
zeta and `256⁻¹`, reduced (`scale_val`): the specification's last layer and
its scaling (`lastInv_val`).

Each butterfly's code is symbolically executed once, for any state, length
and offset (`bfly_run`, …): it stores its `op` of the two words (`bfly_core`,
`bflyC_core`, `bflyInv_core`, `bflyInvS_core`), which is what `CoreOk` states
of a butterfly's code, for the loops below.
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

/-- What the code keeps beside the multiplier `z`: its `zp`, or with `umaal`
(`u`) its `zsN`. -/
def zw (u : Bool) (z : BitVec 32) : BitVec 32 := if u then bzs z else bquot z

theorem zw_false (z : BitVec 32) : zw false z = bquot z := rfl

theorem zw_true (z : BitVec 32) : zw true z = bzs z := rfl

/-- What `mulzV u acc b t Z ZS` leaves in `acc`, for `z` in `Z` and `zs` in `ZS`. -/
def bmulzV (u : Bool) (b z zs : BitVec 32) : BitVec 32 := if u then bmulzU b z zs else bmulz b z zs

/-- The reduced product of `y` and the zeta `z`, as `mulzV u` leaves it. -/
abbrev bprod (u : Bool) (y : BitVec 32) (z : Zq) : BitVec 32 := bmulzV u y (zb z) (zw u (zb z))

/-- The reduced product is less than `2q`. -/
theorem bprod_lt (u : Bool) (y : BitVec 32) (z : Zq) : (bprod u y z).toNat < 2 * q := by
  have hz : (zb z).toNat < q := by rw [toNat_val]; exact z.isLt
  cases u
  · exact (bmulz_toNat y hz).symm ▸ Nat.lt_of_le_of_lt (mulzN_le y.isLt hz) redMax_lt
  · exact (bmulzU_toNat y hz).symm ▸ (mulzUN_bounds y.isLt).2

/-- The reduced product is congruent to the product. -/
theorem bprod_mod (u : Bool) (y : BitVec 32) (z : Zq) : (bprod u y z).toNat % q = y.toNat * z.val % q := by
  have hz : (zb z).toNat < q := by rw [toNat_val]; exact z.isLt
  cases u
  · exact (congrArg (· % q) (bmulz_toNat y hz)).trans (by rw [mulzN_mod y.isLt hz, toNat_val])
  · exact (congrArg (· % q) (bmulzU_toNat y hz)).trans (by rw [mulzUN_mod y.isLt, toNat_val])

/-! ## The forward butterfly -/

/-- The reduced product of the word `y` and the zeta. -/
def prodF (u : Bool) (y : Word) (z : Zq) : Nat := (bprod u (wb y) z).toNat

theorem prodF_lt (u : Bool) (y : Word) (z : Zq) : prodF u y z < 2 * q := bprod_lt u _ z

theorem prodF_mod (u : Bool) (y : Word) (z : Zq) : prodF u y z % q = z.val * y.val % q := by
  rw [prodF, bprod_mod, wb_toNat, Nat.mul_comm]

/-- What the forward butterfly stores: `x + t` and `x + 2q - t`, as words. -/
def opF (u : Bool) (x y : Word) (z : Zq) : Word × Word :=
  (toW (wb x + bprod u (wb y) z), toW (wb x + 16760834 - bprod u (wb y) z))

theorem opF_values (u : Bool) (x y : Word) (z : Zq) (hx : x.val < 15 * q) :
    (opF u x y z).1.val = x.val + prodF u y z ∧ (opF u x y z).2.val = x.val + 2 * q - prodF u y z := by
  have ht : prodF u y z < 2 * 8380417 := prodF_lt u y z
  obtain e : (bprod u (wb y) z).toNat = prodF u y z := rfl
  have hx' := wb_toNat x
  simp only [opF, toW_val]
  generalize prodF u y z = P at e ht ⊢
  generalize bprod u (wb y) z = T at e ⊢
  generalize wb x = X at hx' ⊢
  rw [q_eq] at hx ⊢
  constructor <;> bv_omega

theorem opF_bound (u : Bool) (x y : Word) (z : Zq) {b : Nat} (hb : b ≤ 15) (hx : x.val < b * q) :
    (opF u x y z).1.val < (b + 2) * q ∧ (opF u x y z).2.val < (b + 2) * q := by
  have hv := opF_values u x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb))
  have ht := prodF_lt u y z
  rw [hv.1, hv.2, Nat.add_mul]
  omega_using [hx, ht]

theorem opF_residue (u : Bool) (x y : Word) (z : Zq) (hx : x.val < 15 * q) :
    residue (opF u x y z).1 = residue x + z * residue y ∧
    residue (opF u x y z).2 = residue x - z * residue y := by
  have hv := opF_values u x y z hx
  have ht := prodF_lt u y z
  have hm' : (z * residue y).val = prodF u y z % q := by
    rw [Fin.val_mul, residue, Fin.val_ofNat, Nat.mul_mod_mod, prodF_mod]
  constructor
  · apply Fin.ext
    rw [Fin.val_add, hm']
    change (opF u x y z).1.val % q = (x.val % q + prodF u y z % q) % q
    rw [hv.1, Nat.add_mod]
  · apply Fin.ext
    rw [Fin.val_sub, hm']
    change (opF u x y z).2.val % q = (q - prodF u y z % q + x.val % q) % q
    rw [hv.2]
    have ht' : prodF u y z < 2 * 8380417 := ht
    generalize prodF u y z = P at ht' ⊢
    change (x.val + 2 * 8380417 - P) % 8380417 = (8380417 - P % 8380417 + x.val % 8380417) % 8380417
    omega_using [ht']

/-! ## The inverse butterfly -/

/-- The reduced product of the zeta and `x + 128 q - y`. -/
def prodI (u : Bool) (x y : Word) (z : Zq) : Nat := (bprod u (wb x + 1072693376 - wb y) z).toNat

/-- What the inverse butterfly stores: `x + y`, and the reduced product of
the zeta and `x + 128 q - y`, as words. -/
def opI (u : Bool) (x y : Word) (z : Zq) : Word × Word :=
  (toW (wb x + wb y), toW (bprod u (wb x + 1072693376 - wb y) z))

theorem opI_values (u : Bool) (x y : Word) (z : Zq) (hx : x.val < 128 * q) (hy : y.val < 128 * q) :
    (opI u x y z).1.val = x.val + y.val ∧ (opI u x y z).2.val = prodI u x y z ∧
      prodI u x y z < 2 * q ∧ prodI u x y z % q = z.val * (x.val + 128 * q - y.val) % q := by
  have hx' := wb_toNat x
  have hy' := wb_toNat y
  have hx2 : x.val < 128 * 8380417 := hx
  have hy2 : y.val < 128 * 8380417 := hy
  have hd : (wb x + 1072693376 - wb y).toNat = x.val + 128 * q - y.val := by
    rw [q_eq]
    generalize wb x = X at hx' ⊢
    generalize wb y = Y at hy' ⊢
    bv_omega
  refine ⟨?_, ?_, bprod_lt u _ z, ?_⟩
  · simp only [opI, toW_val]
    generalize wb x = X at hx' ⊢
    generalize wb y = Y at hy' ⊢
    bv_omega
  · simp only [opI, toW_val, prodI]
  · rw [prodI, bprod_mod, hd, Nat.mul_comm]

theorem opI_bound (u : Bool) (x y : Word) (z : Zq) {b : Nat} (hb : 1 ≤ b) (hb' : b ≤ 128) (hx : x.val < b * q)
    (hy : y.val < b * q) : (opI u x y z).1.val < 2 * b * q ∧ (opI u x y z).2.val < 2 * b * q := by
  have hv := opI_values u x y z (Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right q hb'))
    (Nat.lt_of_lt_of_le hy (Nat.mul_le_mul_right q hb'))
  rw [hv.1, hv.2.1, Nat.mul_assoc]
  constructor
  · omega_using [hx, hy]
  · exact Nat.lt_of_lt_of_le hv.2.2.1 (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left q hb))

theorem opI_residue (u : Bool) (x y : Word) (z : Zq) (hx : x.val < 128 * q) (hy : y.val < 128 * q) :
    residue (opI u x y z).1 = residue x + residue y ∧
    residue (opI u x y z).2 = z * (residue x - residue y) := by
  have hv := opI_values u x y z hx hy
  constructor
  · apply Fin.ext
    rw [Fin.val_add]
    change (opI u x y z).1.val % q = (x.val % q + y.val % q) % q
    rw [hv.1, Nat.add_mod]
  · apply Fin.ext
    change (opI u x y z).2.val % q = (z * (residue x - residue y)).val
    rw [hv.2.1, hv.2.2.2, Fin.val_mul, Fin.val_sub, residue, residue, Fin.val_ofNat, Fin.val_ofNat]
    have hl : (x.val + 128 * q - y.val) % q = (q - y.val % q + x.val % q) % q := by
      rw [q_eq] at hx hy ⊢; omega_using [hy]
    rw [Nat.mul_mod, hl, Nat.mul_mod z.val ((q - y.val % q + x.val % q) % q), Nat.mod_mod]

/-- The inverse butterfly with the negated zeta, as the code multiplies by
`negZetaTab`. -/
def opIn (u : Bool) (x y : Word) (z : Zq) : Word × Word := opI u x y (-z)

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
def layerF (u : Bool) (F : LPoly) (len : Nat) : LPoly :=
  Lazy.layF (lblk (opF u) zetas) F len (fun c => 128 / len + c) (128 / len)

/-- A layer of the inverse butterflies on words. -/
def layerI (u : Bool) (F : LPoly) (len : Nat) : LPoly :=
  Lazy.layF (lblk (opI u) fun k => -zetas k) F len (fun c => 256 / len - 1 - c) (128 / len)

theorem lblkF_ok (u : Bool) : Lazy.BlkOk (lblk (opF u) zetas) (opF u) := Lazy.block_ok (opF u)

theorem lblkI_ok (u : Bool) : Lazy.BlkOk (lblk (opI u) fun k => -zetas k) (opIn u) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => Lazy.blockN_add _ _ _ _ _ _ _,
    fun f _ _ _ _ hl ht hs _ hi => Lazy.blockN_bfly_get' (opI u) f hl ht hs hi⟩

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

theorem layerF_rel (u : Bool) {b : Nat} (hb : b ≤ 15) {F : LPoly} {f : Poly} (hF : Rel b F f)
    {len : Nat} (hlen : len ∈ nttLens) : Rel (b + 2) (layerF u F len) (nttLayer f len) := by
  have hl := len_facts hlen
  intro i hi
  rw [layerF, Lazy.layF_get (lblkF_ok u) F hl.1 _ (by omega) hi,
    nttLayer_eq, layF_get nttBlk_ok f hl.1 _ (by omega) hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    exact ⟨(opF_bound u _ _ _ hb h0.1).1, by
      rw [(opF_residue u _ _ _ (Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb))).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega_using [hi])
    have h1 := hF i hi
    exact ⟨(opF_bound u _ _ _ hb h0.1).2, by
      rw [(opF_residue u _ _ _ (Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb))).2, h0.2, h1.2]⟩

theorem layerI_rel (u : Bool) {b : Nat} (hb : 1 ≤ b) (hb' : b ≤ 128) {F : LPoly} {f : Poly}
    (hF : Rel b F f) {len : Nat} (hlen : len ∈ nttLens) : Rel (2 * b) (layerI u F len) (nttInvLayer f len) := by
  have hl := len_facts hlen
  have lt : ∀ {x : Word}, x.val < b * q → x.val < 128 * q := fun h =>
    Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right q hb')
  intro i hi
  rw [layerI, Lazy.layF_get (lblkI_ok u) F hl.1 _ (by omega) hi,
    nttInvLayer_eq, layF_get nttInvBlk_ok f hl.1 _ (by omega) hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    exact ⟨(opI_bound u _ _ (-_) hb hb' h0.1 h1.1).1, by
      rw [opIn, (opI_residue u _ _ _ (lt h0.1) (lt h1.1)).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega_using [hi])
    have h1 := hF i hi
    refine ⟨(opI_bound u _ _ (-_) hb hb' h0.1 h1.1).2, ?_⟩
    rw [opIn, (opI_residue u _ _ _ (lt h0.1) (lt h1.1)).2, h0.2, h1.2]
    exact neg_mul_sub _ _ _

/-- The layers `ls` of `NTT`, from words less than `b q`. -/
theorem layersF_rel (u : Bool) : ∀ (ls : List Nat) (b : Nat) (F : LPoly) (f : Poly), (∀ len ∈ ls, len ∈ nttLens) →
    b + 2 * ls.length ≤ 17 → Rel b F f → Rel (b + 2 * ls.length) (ls.foldl (layerF u) F) (ls.foldl nttLayer f)
  | [], _, _, _, _, _, h => h
  | len :: ls, b, F, f, hls, hb, h => by
    rw [List.length_cons] at hb
    have := layersF_rel u ls (b + 2) (layerF u F len) (nttLayer f len) (fun l hl => hls l (List.mem_cons_of_mem _ hl))
      (by omega_using [hb]) (layerF_rel u (by omega_using [hb]) h (hls len (List.mem_cons_self ..)))
    rw [List.length_cons, show b + 2 * (ls.length + 1) = b + 2 + 2 * ls.length by omega_arith]
    exact this

/-- The layers `ls` of `NTT⁻¹`, from words less than `b q`. -/
theorem layersI_rel (u : Bool) : ∀ (ls : List Nat) (b : Nat) (F : LPoly) (f : Poly), (∀ len ∈ ls, len ∈ nttLens) →
    1 ≤ b → b * 2 ^ ls.length ≤ 256 → Rel b F f →
    Rel (b * 2 ^ ls.length) (ls.foldl (layerI u) F) (ls.foldl nttInvLayer f)
  | [], b, _, _, _, _, _, h => by rw [List.length_nil, Nat.pow_zero, Nat.mul_one]; exact h
  | len :: ls, b, F, f, hls, hb1, hb, h => by
    rw [List.length_cons, Nat.pow_succ, Nat.mul_comm _ 2, ← Nat.mul_assoc, Nat.mul_comm b 2] at hb ⊢
    have h2 : 2 * b ≤ 256 := Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hb
    exact layersI_rel u ls (2 * b) (layerI u F len) (nttInvLayer f len)
      (fun l hl => hls l (List.mem_cons_of_mem _ hl)) (by omega_using [hb1]) hb
      (layerI_rel u hb1 (by omega_using [h2]) h (hls len (List.mem_cons_self ..)))

/-! ## The last layers -/

/-- A word reduced is its residue. -/
theorem canon_val {v : BitVec 32} {x : Word} (hv : v.toNat = x.val) : (bcsub (bred v)).toNat = (residue x).val := by
  have hr := red23_le (x := v.toNat) v.isLt
  rw [bcsub_toNat (by rw [bred_toNat]; exact Nat.lt_of_le_of_lt hr redMax_lt), bred_toNat, red23_mod, hv,
    Fin.val_ofNat]

/-- A word times a zeta, reduced, is the product of its residue and the zeta. -/
theorem scale_val (u : Bool) {v : BitVec 32} {x : Word} (hv : v.toNat = x.val) (z : Zq) :
    (bcsub (bprod u v z)).toNat = (residue x * z).val := by
  rw [bcsub_toNat (bprod_lt u v z), bprod_mod, hv, Fin.val_mul, Fin.val_ofNat, Nat.mod_mul_mod]

/-- The multiplier of the scaling of `NTT⁻¹`. -/
abbrev cInv : Zq := 8347681

/-- What a butterfly of the last layer of `NTT` stores: `opF`, reduced. -/
def opFC (u : Bool) (x y : Word) (z : Zq) : Word × Word :=
  (toW (bcsub (bred (wb x + bprod u (wb y) z))), toW (bcsub (bred (wb x + 16760834 - bprod u (wb y) z))))

theorem opFC_val (u : Bool) (x y : Word) (z : Zq) :
    (opFC u x y z).1.val = (residue (opF u x y z).1).val ∧ (opFC u x y z).2.val = (residue (opF u x y z).2).val := by
  constructor
  · show (toW (bcsub (bred (wb x + bprod u (wb y) z)))).val = _
    rw [toW_val, canon_val (toW_val _).symm]; rfl
  · show (toW (bcsub (bred (wb x + 16760834 - bprod u (wb y) z)))).val = _
    rw [toW_val, canon_val (toW_val _).symm]; rfl

/-- The last layer of `NTT` on words. -/
def layerFC (u : Bool) (F : LPoly) (len : Nat) : LPoly :=
  Lazy.layF (lblk (opFC u) zetas) F len (fun c => 128 / len + c) (128 / len)

theorem lblkFC_ok (u : Bool) : Lazy.BlkOk (lblk (opFC u) zetas) (opFC u) := Lazy.block_ok (opFC u)

/-- The last layer of `NTT` leaves the specification's coefficients. -/
theorem layerFC_val (u : Bool) {b : Nat} (hb : b ≤ 15) {F : LPoly} {f : Poly} (hF : Rel b F f) {len : Nat}
    (hlen : len ∈ nttLens) {i : Nat} (hi : i < 256) :
    ((layerFC u F len)[i]!).val = ((nttLayer f len)[i]!).val := by
  have hl := len_facts hlen
  have lt : ∀ {x : Word}, x.val < b * q → x.val < 15 * q := fun h =>
    Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right q hb)
  rw [layerFC, Lazy.layF_get (lblkFC_ok u) F hl.1 _ (by omega) hi,
    nttLayer_eq, layF_get nttBlk_ok f hl.1 _ (by omega) hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    rw [(opFC_val u _ _ _).1, (opF_residue u _ _ _ (lt h0.1)).1, h0.2, h1.2]
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega_using [hi])
    have h1 := hF i hi
    rw [(opFC_val u _ _ _).2, (opF_residue u _ _ _ (lt h0.1)).2, h0.2, h1.2]

/-- What a butterfly of the last layer of `NTT⁻¹` stores: the sum times
`256⁻¹`, and the difference times the zeta and `256⁻¹`, reduced. -/
def opIS (u : Bool) (x y : Word) (z : Zq) : Word × Word :=
  (toW (bcsub (bprod u (wb x + wb y) cInv)), toW (bcsub (bprod u (wb x + 1072693376 - wb y) (z * cInv))))

theorem opIS_val (u : Bool) (x y : Word) (z : Zq) (hx : x.val < 128 * q) (hy : y.val < 128 * q) :
    (opIS u x y z).1.val = ((residue x + residue y) * cInv).val ∧
    (opIS u x y z).2.val = ((residue x - residue y) * (z * cInv)).val := by
  have hr := opI_residue u x y z hx hy
  constructor
  · show (toW (bcsub (bprod u (wb x + wb y) cInv))).val = _
    rw [toW_val, scale_val u (x := (opI u x y z).1) (toW_val _).symm, hr.1]
  · have hx' := wb_toNat x
    have hy' := wb_toNat y
    have hx2 : x.val < 128 * 8380417 := hx
    have hy2 : y.val < 128 * 8380417 := hy
    have hd : (wb x + 1072693376 - wb y).toNat = x.val + 128 * 8380417 - y.val := by
      generalize wb x = X at hx' ⊢
      generalize wb y = Y at hy' ⊢
      bv_omega
    have e : residue (toW (wb x + 1072693376 - wb y)) = residue x - residue y := by
      apply Fin.ext
      rw [Fin.val_sub]
      show (toW (wb x + 1072693376 - wb y)).val % 8380417 = (8380417 - y.val % 8380417 + x.val % 8380417) % 8380417
      rw [toW_val, hd]
      omega_using [hy2]
    show (toW (bcsub (bprod u (wb x + 1072693376 - wb y) (z * cInv)))).val = _
    rw [toW_val, scale_val u (toW_val _).symm, e]

/-- Algorithm 42 multiplies the difference `x - y` by `-ζ`, and the result by
`256⁻¹`. -/
theorem neg_mul_scale (z c a b : Zq) : (a - b) * (-z * c) = z * (b - a) * c := by
  grind

/-- The last layer of `NTT⁻¹`, coefficient by coefficient. -/
theorem lastInv_get (g : Poly) {i : Nat} (hi : i < 256) :
    (nttInvLayer g 128)[i]! = if i < 128 then g[i]! + g[i + 128]! else zetas 1 * (g[i]! - g[i - 128]!) := by
  rw [nttInvLayer_eq, layF_get nttInvBlk_ok g (by decide) _ (by decide) hi,
    ite_eq_left (show i < 2 * 128 * (128 / 128) from hi), Nat.mod_eq_of_lt (show i < 2 * 128 from hi),
    Nat.div_eq_of_lt (show i < 2 * 128 from hi)]

/-- The last layer of `NTT⁻¹` and the scaling leave the specification's
coefficients. -/
theorem lastInv_val (u : Bool) {F : LPoly} {f : Poly} (hF : Rel 128 F f) {i : Nat} (hi : i < 256) :
    ((Lazy.blockN (Lazy.bfly (opIS u)) F 128 (-zetas 1) 0 128)[i]!).val =
      (((nttInvLayer f 128).map (· * cInv))[i]!).val := by
  rw [Lazy.blockN_bfly_get' (opIS u) F (by decide) (Nat.le_refl _) (by decide) hi,
    map_mul_get _ _ (by rw [n_eq]; exact hi), lastInv_get f hi]
  by_cases h : i < 128
  · have h0 := hF i hi
    have h1 := hF (i + 128) (by omega_using [h])
    rw [ite_eq_left (show 0 ≤ i ∧ i < 0 + 128 from ⟨Nat.zero_le _, by omega_using [h]⟩), ite_eq_left h,
      (opIS_val u _ _ _ h0.1 h1.1).1, h0.2, h1.2]
  · have h0 := hF (i - 128) (by omega_using [hi])
    have h1 := hF i hi
    rw [ite_eq_right (show ¬ (0 ≤ i ∧ i < 0 + 128) from fun e => h (by omega_using [e.2])),
      ite_eq_left (show 0 + 128 ≤ i ∧ i < 0 + 128 + 128 from ⟨by omega_using [h], by omega_using [hi]⟩),
      ite_eq_right h, (opIS_val u _ _ _ h0.1 h1.1).2, h0.2, h1.2, neg_mul_scale]

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

/-- `-q`, `q`, and the zeta `z` with what goes with it (`zw`), in `r4`–`r7`. -/
def ZetaIn (u : Bool) (z : Zq) (s : State) : Prop :=
  s.gpr .r4 = Nw ∧ s.gpr .r5 = Qw ∧ s.gpr .r6 = zb z ∧ s.gpr .r7 = zw u (zb z)

/-- The registers of the last layer of `NTT⁻¹`: `ZetaIn` of the zeta times
`256⁻¹`, and `256⁻¹` with what goes with it in `r1` and `r2`. -/
def ScaleIn (u : Bool) (z : Zq) (s : State) : Prop :=
  ZetaIn u (z * cInv) s ∧ s.gpr .r1 = zb cInv ∧ s.gpr .r2 = zw u (zb cInv)

/-- The registers the loops of the transforms keep. -/
abbrev bflyKeep : List Reg := [.r1, .r2, .r4, .r5, .r6, .r7, .r11, .lr]

/-- The registers a butterfly keeps. -/
abbrev coreKeep : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r11, .lr]

theorem ZetaIn.keep {u : Bool} {z : Zq} {s s' : State} (hk : Keep bflyKeep s s') (h : ZetaIn u z s) :
    ZetaIn u z s' :=
  ⟨(hk.gpr .r4 (by decide)).trans h.1, (hk.gpr .r5 (by decide)).trans h.2.1,
    (hk.gpr .r6 (by decide)).trans h.2.2.1, (hk.gpr .r7 (by decide)).trans h.2.2.2⟩

theorem ScaleIn.keep {u : Bool} {z : Zq} {s s' : State} (hk : Keep bflyKeep s s') (h : ScaleIn u z s) :
    ScaleIn u z s' :=
  ⟨h.1.keep hk, (hk.gpr .r1 (by decide)).trans h.2.1, (hk.gpr .r2 (by decide)).trans h.2.2⟩

/-- The code `code len o` stores what the butterfly `op` gives of the words
`j + o` and `j + o + len` of the polynomial at `p`, with `r0` pointing at
coefficient `j` and the registers as `C` says for the zeta. -/
def CoreOk (code : Nat → Nat → List Instr) (op : Word → Word → Zq → Word × Word) (C : Zq → State → Prop) : Prop :=
  ∀ (p : BitVec 32) (len j o : Nat), 0 < len → len ≤ 128 → o < 4 → j + o + len < 256 → p.toNat + 1024 ≤ 2 ^ 32 →
    ∀ (z : Zq) (G : LPoly) (s : State), s.gpr .r0 = p + BitVec.ofNat 32 (4 * j) → C z s →
      LP s.mem (State.addr p) G → polyRegion (State.addr p) ∈ s.wr →
      WP isa (.block (code len o)) s fun s' =>
        LP s'.mem (State.addr p) (Lazy.bfly op G (j + o) len z) ∧ Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        Keep coreKeep s s'

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

/-- The word stored for a coefficient. -/
theorem word_val {m : Mem} {P : Addr} {G : LPoly} (h : LP m P G) {j : Nat} (hj : j < 256) :
    m.readW (coeffAddr P j) 32 = wb G[j]! := by
  rw [← coeffAt_eq]; exact wb_of (h j hj)

theorem q_shl1 : Qw <<< 1 = 16760834 := by decide

theorem q_shl7 : Qw <<< 7 = 1072693376 := by decide

/-! ## The butterflies, symbolically -/

section
variable (u : Bool) {s : State} {x z zp f fp : BitVec 32} {len o : Nat} (ho : 4 * (o + len) < 4096)
  (h0 : s.gpr .r0 = x)
  (h4 : s.gpr .r4 = Nw) (h5 : s.gpr .r5 = Qw) (h6 : s.gpr .r6 = z) (h7 : s.gpr .r7 = zp)
  (iA : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * o))) 4)
  (iB : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 4)
  (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * o))) 4)
  (oB : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 4)
include ho h0 h4 h5 h6 h7 iA iB oA oB

theorem bfly_run :
    WP isa (.block (Impl.MlDsa.Arm.Arith.bfly u len o)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * (o + len))))
          (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 + 16760834 -
            bmulzV u (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) z zp)).writeW
        (State.addr (x + BitVec.ofNat 32 (4 * o)))
          (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 +
            bmulzV u (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) z zp) ∧
      Keep coreKeep s s' := by
  have ho' : 4 * o < 4096 := by omega_using [ho]
  cases u <;>
  · run_block [Impl.MlDsa.Arm.Arith.bfly, mulzV, mulzU, red, mulq, bmulzV, bmulzU, bmulz, bmulq, bred, h0, h4, h5, h6,
      h7, iA, iB, oA, oB, ho, ho', q_shl1, Bool.false_eq_true]
    keep_simp

theorem bflyC_run :
    WP isa (.block (bflyC u len o)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * (o + len))))
          (bcsub (bred (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 + 16760834 -
            bmulzV u (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) z zp)))).writeW
        (State.addr (x + BitVec.ofNat 32 (4 * o)))
          (bcsub (bred (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 +
            bmulzV u (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) z zp))) ∧
      Keep coreKeep s s' := by
  have ho' : 4 * o < 4096 := by omega_using [ho]
  cases u <;>
  · run_block [bflyC, mulzV, mulzU, red, mulq, csub, bmulzV, bmulzU, bmulz, bmulq, bred, bcsub, h0, h4, h5, h6, h7,
      iA, iB, oA, oB, ho, ho', q_shl1, Bool.false_eq_true]
    keep_simp

theorem bflyInv_run :
    WP isa (.block (Impl.MlDsa.Arm.Arith.bflyInv u len o)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * o)))
          (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 +
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32)).writeW
        (State.addr (x + BitVec.ofNat 32 (4 * (o + len))))
          (bmulzV u (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 + 1072693376 -
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) z zp) ∧
      Keep coreKeep s s' := by
  have ho' : 4 * o < 4096 := by omega_using [ho]
  cases u <;>
  · run_block [Impl.MlDsa.Arm.Arith.bflyInv, mulzV, mulzU, red, mulq, bmulzV, bmulzU, bmulz, bmulq, bred, h0, h4, h5,
      h6, h7, iA, iB, oA, oB, ho, ho', q_shl7, Bool.false_eq_true]
    keep_simp

theorem bflyInvS_run (h1 : s.gpr .r1 = f) (h2 : s.gpr .r2 = fp) :
    WP isa (.block (bflyInvS u len o)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * o)))
          (bcsub (bmulzV u (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 +
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) f fp))).writeW
        (State.addr (x + BitVec.ofNat 32 (4 * (o + len))))
          (bcsub (bmulzV u (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 + 1072693376 -
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) z zp)) ∧
      Keep coreKeep s s' := by
  have ho' : 4 * o < 4096 := by omega_using [ho]
  cases u <;>
  · run_block [bflyInvS, mulzV, mulzU, red, mulq, csub, bmulzV, bmulzU, bmulz, bmulq, bred, bcsub, h0, h1, h2, h4,
      h5, h6, h7, iA, iB, oA, oB, ho, ho', q_shl7, Bool.false_eq_true]
    keep_simp

end

/-! ## What the butterflies store -/

theorem bfly_core (u : Bool) : CoreOk (Impl.MlDsa.Arm.Arith.bfly u) (opF u) (ZetaIn u) := by
  intro p len j o hl hl' ho hj hp z G s h0 ⟨z4, z5, z6, z7⟩ hG hw
  have eA := addr_at hp (j := j) (k := o) (by omega_using [hj])
  have eB := addr_at hp (j := j) (k := o + len) (by omega_using [hj])
  have hjo : j + o < 256 := by omega_using [hj]
  have hjn : j + o < n := by rw [n_eq]; exact hjo
  have hjl : j + o + len < n := by rw [n_eq]; exact hj
  rw [← Nat.add_assoc] at eB
  refine WP.mono (bfly_run u (len := len) (o := o) (by omega_using [hl', ho]) h0 z4 z5 z6 z7
    (by rw [eA]; exact rd_at hw hjo) (by rw [eB]; exact rd_at hw hj)
    (by rw [eA]; exact wr_at hw hjo) (by rw [eB]; exact wr_at hw hj)) fun s' ⟨hm, hk⟩ => ⟨?_, ?_, hk⟩
  · rw [hm, eA, eB, word_val hG hjo, word_val hG hj]
    exact lp_bfly hG (opF u) hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjl)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjn)

theorem bflyC_core (u : Bool) : CoreOk (bflyC u) (opFC u) (ZetaIn u) := by
  intro p len j o hl hl' ho hj hp z G s h0 ⟨z4, z5, z6, z7⟩ hG hw
  have eA := addr_at hp (j := j) (k := o) (by omega_using [hj])
  have eB := addr_at hp (j := j) (k := o + len) (by omega_using [hj])
  have hjo : j + o < 256 := by omega_using [hj]
  have hjn : j + o < n := by rw [n_eq]; exact hjo
  have hjl : j + o + len < n := by rw [n_eq]; exact hj
  rw [← Nat.add_assoc] at eB
  refine WP.mono (bflyC_run u (len := len) (o := o) (by omega_using [hl', ho]) h0 z4 z5 z6 z7
    (by rw [eA]; exact rd_at hw hjo) (by rw [eB]; exact rd_at hw hj)
    (by rw [eA]; exact wr_at hw hjo) (by rw [eB]; exact wr_at hw hj)) fun s' ⟨hm, hk⟩ => ⟨?_, ?_, hk⟩
  · rw [hm, eA, eB, word_val hG hjo, word_val hG hj]
    exact lp_bfly hG (opFC u) hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjl)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjn)

theorem bflyInv_core (u : Bool) : CoreOk (Impl.MlDsa.Arm.Arith.bflyInv u) (opI u) (ZetaIn u) := by
  intro p len j o hl hl' ho hj hp z G s h0 ⟨z4, z5, z6, z7⟩ hG hw
  have eA := addr_at hp (j := j) (k := o) (by omega_using [hj])
  have eB := addr_at hp (j := j) (k := o + len) (by omega_using [hj])
  have hjo : j + o < 256 := by omega_using [hj]
  have hjn : j + o < n := by rw [n_eq]; exact hjo
  have hjl : j + o + len < n := by rw [n_eq]; exact hj
  rw [← Nat.add_assoc] at eB
  refine WP.mono (bflyInv_run u (len := len) (o := o) (by omega_using [hl', ho]) h0 z4 z5 z6 z7
    (by rw [eA]; exact rd_at hw hjo) (by rw [eB]; exact rd_at hw hj)
    (by rw [eA]; exact wr_at hw hjo) (by rw [eB]; exact wr_at hw hj)) fun s' ⟨hm, hk⟩ => ⟨?_, ?_, hk⟩
  · rw [hm, eA, eB, word_val hG hjo, word_val hG hj]
    exact lp_bflyInv hG (opI u) hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjn)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjl)

theorem bflyInvS_core (u : Bool) : CoreOk (bflyInvS u) (opIS u) (ScaleIn u) := by
  intro p len j o hl hl' ho hj hp z G s h0 ⟨⟨z4, z5, z6, z7⟩, z1, z2⟩ hG hw
  have eA := addr_at hp (j := j) (k := o) (by omega_using [hj])
  have eB := addr_at hp (j := j) (k := o + len) (by omega_using [hj])
  have hjo : j + o < 256 := by omega_using [hj]
  have hjn : j + o < n := by rw [n_eq]; exact hjo
  have hjl : j + o + len < n := by rw [n_eq]; exact hj
  rw [← Nat.add_assoc] at eB
  refine WP.mono (bflyInvS_run u (len := len) (o := o) (by omega_using [hl', ho]) h0 z4 z5 z6 z7
    (by rw [eA]; exact rd_at hw hjo) (by rw [eB]; exact rd_at hw hj)
    (by rw [eA]; exact wr_at hw hjo) (by rw [eB]; exact wr_at hw hj) z1 z2) fun s' ⟨hm, hk⟩ => ⟨?_, ?_, hk⟩
  · rw [hm, eA, eB, word_val hG hjo, word_val hG hj]
    exact lp_bflyInv hG (opIS u) hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjn)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjl)

end VG.Proof.MlDsa.Arm.Arith

end

end



/-!
# ML-DSA on 32-bit ARM: the table, blocks and layers of `NTT` and `NTT⁻¹`

`storeTab t 256` leaves the `u32`s `t 0, …, t 255` at `r1` (`Tab`,
`storeTab_ok`): of the zeta `z`, `z` itself or with `umaal` its `zsN`
(`tabOf`, `tw`), from which a block takes `z` and what goes with it
(`zetaPre_ok`, `zw`). The rest is for any butterfly code that does what a butterfly
`op` does (`CoreOk`): butterflies in a row (`grp_ok`, `Lazy.blockN`), the
loop over groups of four (`grpLoop_ok`), a block of either kind (`blkS_ok`,
`blkL_ok`, which prove `BlockOk`), and a layer of any program that is such a
block (`lay_ok`, `Lazy.layF`), on words, with the zetas `Z (zi c)`, whose
values `tab` the table at `zB` holds.
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

/-- What the code's table holds of the zeta `z`: `z`, or with `umaal` its `zsN`. -/
def tw (u : Bool) (z : Zq) : BitVec 32 := if u then bzs (zb z) else zb z

/-- The entries of the code's table of the zetas `Z` are `tw`. -/
theorem tabOf_word (u : Bool) {tab : Nat → Nat} {Z : Nat → Zq} (hZ : TabOf tab Z) {k : Nat} (hk : k < 256) :
    BitVec.ofNat 32 (tabOf u tab k) = tw u (Z k) := by
  cases u
  · simp only [tabOf, tw, Bool.false_eq_true, ite_false, hZ k hk]
  · simp only [tabOf, tw, ite_true, hZ k hk, bzs, toNat_val]
    rfl

/-- The entries of the code's table of values less than `q` fit in a word. -/
theorem tabOf_lt (u : Bool) {tab : Nat → Nat} (ht : ∀ k < 256, tab k < q) : ∀ k < 256, tabOf u tab k < 2 ^ 32 := by
  intro k hk
  cases u
  · simp only [tabOf, Bool.false_eq_true, ite_false]
    exact Nat.lt_trans (ht k hk) (by decide)
  · exact zsN_lt (ht k hk)

theorem tab_word {t : Nat → Nat} (ht : ∀ k < 256, t k < 2 ^ 32) (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 (t i / 65536) ++ ((BitVec.ofNat 16 (t i % 65536)).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 (t i) := by
  have := ht i hi
  generalize t i = v at *
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_zero, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega_using [])]
  omega_using []

theorem tabStep_ok (t : Nat → Nat) (ht : ∀ k < 256, t k < 2 ^ 32) {i : Nat} (hi : i < 256) (s : State) {zB : BitVec 32}
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
theorem storeTab_ok (t : Nat → Nat) (ht : ∀ k < 256, t k < 2 ^ 32) (s : State) {zB : BitVec 32}
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

/-! ## Butterflies in a row -/

theorem ptr_step (p : BitVec 32) (a : Nat) (c : BitVec 32) (b : Nat) (hc : c = BitVec.ofNat 32 (4 * b)) :
    p + BitVec.ofNat 32 (4 * a) + c = p + BitVec.ofNat 32 (4 * (a + b)) := by
  rw [hc, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem grpEnd_ok (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm 16), .subs .r3 .r3 (.imm 1)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 + 16 ∧ s'.gpr .r3 = s.gpr .r3 - 1 ∧ s'.z = (s.gpr .r3 - 1 == 0) ∧
        s'.mem = s.mem ∧ Keep bflyKeep s s' := by
  run_block []
  keep_simp

section
variable {code : Nat → Nat → List Instr} {op : Word → Word → Zq → Word × Word} {C : Zq → State → Prop}
  (hb : CoreOk code op C) (hC : ∀ z s s', Keep bflyKeep s s' → C z s → C z s')
include hb hC

/-- `u` butterflies in a row from coefficient `j`, where `r0` points. -/
theorem grp_ok {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {len j u : Nat} (hlen : 0 < len)
    (hl : len ≤ 128) (hu : u ≤ 4) (hj : j + u + len ≤ 256) (z : Zq) (G : LPoly) (s : State)
    (h0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * j)) (hz : C z s) (hG : LP s.mem (State.addr p) G)
    (hw : polyRegion (State.addr p) ∈ s.wr) :
    WP isa (.block (grp (code len) u)) s fun s' =>
      LP s'.mem (State.addr p) (Lazy.blockN (Lazy.bfly op) G len z j u) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ Keep coreKeep s s' := by
  refine wp_range_flatMap (M := isa) (fun k s' => LP s'.mem (State.addr p) (Lazy.blockN (Lazy.bfly op) G len z j k) ∧
      Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ Keep coreKeep s s')
    (fun k s' hk ⟨hP, hf, hk'⟩ => ?_) u (Nat.le_refl _) s ⟨hG, Frame.refl _ _, Keep.refl _ _⟩
  refine WP.mono (hb p len j k hlen hl (by omega_using [hk, hu]) (by omega_using [hk, hj]) hp z _ s'
    ((hk'.gpr .r0 (by decide)).trans h0) (hC z s s' (hk'.mono (by decide)) hz) hP (by rw [hk'.wr]; exact hw))
    fun s'' ⟨hP', hf', hk''⟩ => ⟨by rw [Lazy.blockN_succ]; exact hP', hf.trans hf', hk'.trans hk''⟩

/-- The loop over `N` groups of four butterflies, from coefficient `start`. -/
theorem grpLoop_ok {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {len start N : Nat} (hlen : 0 < len)
    (hl : len ≤ 128) (hN : 0 < N) (hN' : N ≤ 32) (hs : start + 4 * N + len ≤ 256) (z : Zq) (G : LPoly) (s : State)
    (h0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * start)) (hz : C z s) (hG : LP s.mem (State.addr p) G)
    (hw : polyRegion (State.addr p) ∈ s.wr) (h3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (N - 0))) :
    WP isa (grpLoop (code len)) s fun s' =>
      LP s'.mem (State.addr p) (Lazy.blockN (Lazy.bfly op) G len z start (4 * N)) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + 4 * N)) ∧ Keep bflyKeep s s' := by
  refine wp_loop_ne (fun t s' => LP s'.mem (State.addr p) (Lazy.blockN (Lazy.bfly op) G len z start (4 * t)) ∧
      Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + 4 * t)) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (1 * (N - t)) ∧ Keep bflyKeep s s') hN
    (fun t ht s' ⟨hP, hf, h0', h3', hk⟩ => ?_) (fun _ ⟨hP, hf, h0', _, hk⟩ => ⟨hP, hf, h0', hk⟩)
    ⟨hG, Frame.refl _ _, by rw [h0, Nat.mul_zero, Nat.add_zero], h3, Keep.refl _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (grp_ok hb hC hp hlen hl (Nat.le_refl 4) (by omega_using [hs, ht]) z _ s' h0' (hC z s s' hk hz) hP
    (by rw [hk.wr]; exact hw)) fun s₁ ⟨hP₁, hf₁, k₁⟩ => ?_
  refine WP.mono (grpEnd_ok s₁) fun s'' ⟨h0'', h3'', hz'', m'', k₂⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [m'', Nat.mul_succ, Lazy.blockN_add]; exact hP₁
  · rw [m'']; exact hf.trans hf₁
  · rw [h0'', k₁.gpr .r0 (by decide), h0', ptr_step p _ 16 4 rfl,
      show start + 4 * t + 4 = start + 4 * (t + 1) by omega_using []]
  · rw [h3'', k₁.gpr .r3 (by decide), h3']; exact count_sub (k := 1) ht
  · exact hk.trans ((k₁.mono (by decide)).trans k₂)
  · rw [hz'', k₁.gpr .r3 (by decide), h3']; exact count_z (k := 1) ht (by decide) (by omega_using [hN'])

end

/-! ## A block -/

/-- The pointer to the next zeta. -/
def nextZ (op : DpOp) (x : BitVec 32) : BitVec 32 := if op = .add then x + 4 else x - 4

/-- The zeta `z < q` from `zsN z`, as `zetaPre` takes it with `umaal`: the
high word of `zsN z · q + 2³² - 1`. -/
theorem bzs_zeta {z : BitVec 32} (hz : z.toNat < q) :
    BitVec.ofNat 32 (((bzs z).toNat * Qw.toNat + (0 : BitVec 32).toNat + (~~~(0 : BitVec 32)).toNat) / 2 ^ 32) = z := by
  apply BitVec.eq_of_toNat_eq
  have h := zsN_zeta hz
  rw [q_eq] at h
  rw [BitVec.toNat_ofNat, bzs_toNat hz, BitVec.toNat_not, show Qw.toNat = 8380417 from rfl,
    show (0 : BitVec 32).toNat = 0 from rfl]
  obtain h' : (zsN z.toNat * 8380417 + 0 + (2 ^ 32 - 1 - 0)) / 2 ^ 32 = z.toNat := by
    generalize zsN z.toNat = S at h ⊢
    omega_using [h]
  rw [h']
  exact Nat.mod_eq_of_lt z.isLt

theorem zetaPre_ok (u : Bool) (op : DpOp) (hop : op = .add ∨ op = .sub) (s : State) {x : BitVec 32} (z : Zq)
    (h1 : s.gpr .r1 = x) (h5 : s.gpr .r5 = Qw)
    (hi : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (hw : s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 = tw u z) :
    WP isa (.block (zetaPre u op)) s fun s' =>
      s'.gpr .r6 = zb z ∧ s'.gpr .r7 = zw u (zb z) ∧
      s'.gpr .r1 = (if op = .add then x + 4 else x - 4) ∧ s'.mem = s.mem ∧
      Keep [.r0, .r2, .r3, .r4, .r5, .r11, .lr] s s' := by
  have hz : (zb z).toNat < q := by rw [toNat_val]; exact z.isLt
  cases u <;> rcases hop with rfl | rfl <;>
  · run_block [zetaPre, quot, bquot, zw, tw, h1, h5, hi, hw, Bool.false_eq_true, bzs_zeta hz]
    keep_simp

theorem blkEnd_ok (c : Nat) (he : encodable (BitVec.ofNat 32 c) = true) (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 c)), .subs .r2 .r2 (.imm 1)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 c ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧
        s'.z = (s.gpr .r2 - 1 == 0) ∧ s'.mem = s.mem ∧ Keep [.r1, .r4, .r5, .r6, .r7, .r11, .lr] s s' := by
  run_block [he]
  keep_simp

theorem movR3_ok (c : Nat) (he : encodable (BitVec.ofNat 32 c) = true) (s : State) :
    WP isa (.block [.mov .r3 (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      s'.gpr .r3 = BitVec.ofNat 32 c ∧ s'.mem = s.mem ∧
        Keep [.r0, .r1, .r2, .r4, .r5, .r6, .r7, .r11, .lr] s s' := by
  run_block [he]
  keep_simp

/-- The program `blk` is a block of the layer with `len` of the polynomial
at `p`: with `r0` at coefficient `start` and `r1` at entry `k` of the table
`tab` at `zB`, of the zetas `Z`, it runs the `len` butterflies `op` with
`Z k`, and leaves `r0` at the next block, `r1` at the next entry and the
count of blocks in `r2` one less. -/
def BlockOk (blk : Prog isa) (op : Word → Word → Zq → Word × Word) (tab : Nat → Nat) (Z : Nat → Zq) (dop : DpOp)
    (len : Nat) (p zB : BitVec 32) : Prop :=
  ∀ (start k : Nat), start + 2 * len ≤ 256 → k < 256 → ∀ (G : LPoly) (s : State),
    s.gpr .r0 = p + BitVec.ofNat 32 (4 * start) → s.gpr .r1 = zB + BitVec.ofNat 32 (4 * k) → s.gpr .r4 = Nw →
    s.gpr .r5 = Qw → LP s.mem (State.addr p) G → polyRegion (State.addr p) ∈ s.wr →
    polyRegion (State.addr zB) ∈ s.rd ++ s.wr → Tab tab s.mem (State.addr zB) →
    WP isa blk s fun s' =>
      LP s'.mem (State.addr p) (lblk op Z G len k start len) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + 2 * len)) ∧ s'.gpr .r1 = nextZ dop (s.gpr .r1) ∧
        s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧ Keep [.r4, .r5, .r11, .lr] s s'

section
variable {u : Bool} {code : Nat → Nat → List Instr} {op : Word → Word → Zq → Word × Word}
  (hb : CoreOk code op (ZetaIn u))
  {tab : Nat → Nat} {Z : Nat → Zq} (hZ : TabOf tab Z) {p zB : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32)
  (hzf : zB.toNat + 1024 ≤ 2 ^ 32) {len : Nat} (hlen : 0 < len) (dop : DpOp) (hop : dop = .add ∨ dop = .sub)
include hb hZ hp hzf hlen hop

/-- A block of at most four butterflies, in a row. -/
theorem blkS_ok (hl : len ≤ 4) : BlockOk (nttBlkS u (code len) len dop) op (tabOf u tab) Z dop len p zB := by
  intro start k hs hk G s h0 h1 h4 h5 hG hw hzw ht
  have eZ : State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) = coeffAddr (State.addr zB) k :=
    addr_at0 hzf hk
  have hwv : s.mem.readW (State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 32 = tw u (Z k) := by
    rw [eZ, ← coeffAt_eq, ht k hk, tabOf_word u hZ hk]
  have he : encodable (BitVec.ofNat 32 (8 * len)) = true := by
    have : ∀ l < 5, encodable (BitVec.ofNat 32 (8 * l)) = true := by decide
    exact this len (by omega_using [hl])
  rw [nttBlkS, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zetaPre_ok u dop hop s (Z k) h1 h5 (by
    rw [eZ]; exact inRegions_of hzw (coeff_contains _ (show k < n by rw [n_eq]; exact hk))) hwv)
    fun s₁ ⟨e6, e7, e1, m₁, k₁⟩ => ?_
  refine WP.mono (grp_ok hb (fun _ _ _ hk h => h.keep hk) hp hlen (by omega_using [hl]) hl (by omega_using [hs])
    (Z k) G s₁ ((k₁.gpr .r0 (by decide)).trans h0)
    ⟨(k₁.gpr .r4 (by decide)).trans h4, (k₁.gpr .r5 (by decide)).trans h5, e6, e7⟩ (by rw [m₁]; exact hG)
    (by rw [k₁.wr]; exact hw)) fun s₂ ⟨hP, hf, k₂⟩ => ?_
  refine WP.mono (blkEnd_ok (8 * len) he s₂) fun s' ⟨h0', h2', hz', m', k₃⟩ => ⟨by rw [m']; exact hP,
    by rw [m', ← m₁]; exact hf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0', k₂.gpr .r0 (by decide), k₁.gpr .r0 (by decide), h0, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega_using []
  · rw [k₃.gpr .r1 (by decide), k₂.gpr .r1 (by decide), e1, h1]; rfl
  · rw [h2', k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · rw [hz', k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · exact ((k₁.mono (rs' := [.r4, .r5, .r11, .lr]) (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))

/-- A longer block, four butterflies at a time. -/
theorem blkL_ok (hl : len ≤ 128) (hl4 : 4 * (len / 4) = len) :
    BlockOk (nttBlkL u (code len) len dop) op (tabOf u tab) Z dop len p zB := by
  intro start k hs hk G s h0 h1 h4 h5 hG hw hzw ht
  have eZ : State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) = coeffAddr (State.addr zB) k :=
    addr_at0 hzf hk
  have hwv : s.mem.readW (State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 32 = tw u (Z k) := by
    rw [eZ, ← coeffAt_eq, ht k hk, tabOf_word u hZ hk]
  have he : encodable (BitVec.ofNat 32 (4 * len)) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 (4 * l)) = true := by decide
    exact this len (by omega_using [hl])
  have he3 : encodable (BitVec.ofNat 32 (len / 4)) = true := by
    have : ∀ l < 33, encodable (BitVec.ofNat 32 l) = true := by decide
    exact this (len / 4) (by omega_using [hl])
  rw [nttBlkL]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (zetaPre_ok u dop hop s (Z k) h1 h5 (by
    rw [eZ]; exact inRegions_of hzw (coeff_contains _ (show k < n by rw [n_eq]; exact hk))) hwv)
    fun s₁ ⟨e6, e7, e1, m₁, k₁⟩ => ?_
  refine WP.mono (movR3_ok (len / 4) he3 s₁) fun s₂ ⟨e3, m₂, k₂⟩ => ?_
  refine WP.seq (WP.mono (grpLoop_ok hb (fun _ _ _ hk h => h.keep hk) hp hlen hl (N := len / 4) (start := start)
    (by omega_using [hl4, hlen]) (by omega_using [hl]) (by omega_using [hl4, hs]) (Z k) G s₂
    ((k₂.gpr .r0 (by decide)).trans ((k₁.gpr .r0 (by decide)).trans h0))
    ⟨(k₂.gpr .r4 (by decide)).trans ((k₁.gpr .r4 (by decide)).trans h4),
      (k₂.gpr .r5 (by decide)).trans ((k₁.gpr .r5 (by decide)).trans h5),
      (k₂.gpr .r6 (by decide)).trans e6, (k₂.gpr .r7 (by decide)).trans e7⟩
    (by rw [m₂, m₁]; exact hG) (by rw [k₂.wr, k₁.wr]; exact hw) (by rw [e3, Nat.sub_zero, Nat.one_mul]))
    fun s₃ ⟨hP, hf, h0₃, k₃⟩ => ?_)
  rw [hl4] at hP h0₃
  refine WP.mono (blkEnd_ok (4 * len) he s₃) fun s' ⟨h0', h2', hz', m', k₄⟩ => ⟨by rw [m']; exact hP,
    by rw [m', ← m₁, ← m₂]; exact hf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0', h0₃, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega_using []
  · rw [k₄.gpr .r1 (by decide), k₃.gpr .r1 (by decide), k₂.gpr .r1 (by decide), e1, h1]; rfl
  · rw [h2', k₃.gpr .r2 (by decide), k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · rw [hz', k₃.gpr .r2 (by decide), k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · exact (((k₁.mono (rs' := [.r4, .r5, .r11, .lr]) (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))

end

/-! ## A layer -/

theorem layPre_ok (c : Nat) (hc : c ≤ 128) (s : State) :
    WP isa (.block [.mov .r2 (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      s'.gpr .r2 = BitVec.ofNat 32 c ∧ s'.mem = s.mem ∧ Keep [.r0, .r1, .r4, .r5, .r11, .lr] s s' := by
  have he : encodable (BitVec.ofNat 32 c) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 l) = true := by decide
    exact this c (by omega_using [hc])
  run_block [he]
  keep_simp

theorem layPost_ok (s : State) :
    WP isa (.block [.dp .sub .r0 .r0 (.imm 1024)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 - 1024 ∧ s'.mem = s.mem ∧ Keep [.r1, .r4, .r5, .r11, .lr] s s' := by
  run_block []
  keep_simp

/-- The facts about the lengths of the layers. -/
theorem lens_facts : ∀ len ∈ nttLens, 0 < len ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
    128 / len ≤ 128 := by
  decide

/-- A layer, from `r0` = `f` and the zeta of its first block at `r1`. -/
theorem lay_ok {blk : Prog isa} {op : Word → Word → Zq → Word × Word} {tab : Nat → Nat} {Z : Nat → Zq}
    {dop : DpOp} {len : Nat} {p zB : BitVec 32} (hblk : BlockOk blk op tab Z dop len p zB)
    (hlen : len ∈ nttLens) (zi : Nat → Nat) (hzi : ∀ c < 128 / len, zi c < 256)
    (hstep : ∀ c < 128 / len, nextZ dop (zB + BitVec.ofNat 32 (4 * zi c)) = zB + BitVec.ofNat 32 (4 * zi (c + 1)))
    (F : LPoly) (s : State) (h0 : s.gpr .r0 = p) (h1 : s.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi 0))
    (h4 : s.gpr .r4 = Nw) (h5 : s.gpr .r5 = Qw) (hF : LP s.mem (State.addr p) F)
    (hw : polyRegion (State.addr p) ∈ s.wr)
    (hzw : polyRegion (State.addr zB) ∈ s.rd ++ s.wr)
    (hd : (polyRegion (State.addr zB)).Disjoint (polyRegion (State.addr p))) (ht : Tab tab s.mem (State.addr zB)) :
    WP isa (nttLay blk len) s fun s' =>
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
    refine WP.mono (hblk _ _ hcm (hzi c hc) _ s' h0' h1'
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

end VG.Proof.MlDsa.Arm.Arith
