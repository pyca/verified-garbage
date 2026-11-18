module

public import VerifiedGarbage.Proof.MlKem.Ntt
public import VerifiedGarbage.Proof.MlKem.Blocks
public import VerifiedGarbage.Proof.MlKem.NttLayer
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.MlKem.Arm.Ntt
public import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ML-KEM on 32-bit ARM: the reductions, the lazy butterflies' values, the tables and the saved registers

`reduce` computes `x mod q` of any `x < 2²⁵` (`red_toNat`), through
`barrett32` (`Proof/MlKem/Arith.lean`); `mulz` leaves `mulzN b z`, less than
`2q` and congruent to `b z` for `b < 2¹⁶` (`mulzN_bounds`, `bmz_toNat`);
`canon` reduces a word less than `15q` (`bcan_toNat`).

The butterflies store words congruent to the specification's coefficients
(`Rel`), as on RISC-V (`Proof/MlKem/RISCV64/Ntt.lean`): `opF` is what the
forward butterfly stores, and a layer takes words less than `b q` to words
less than `(b + 2) q` (`layerF_rel`); `opI` is the inverse butterfly's, and
a layer keeps words less than `2q` (`layerI_rel`). The last layer of
each transform stores canonical coefficients: `NTT`'s stores `opFC`, `opF`
reduced, and leaves the specification's coefficients from words less than
`13q` (`layerFC_val`); `NTT⁻¹`'s stores `opIS`, the sum times 3303 and the
difference times the zeta and 3303, reduced (`scale_val`), which is the
specification's last layer and its multiplication by 3303 (`lastInv_val`).

`table` stores a table of 128 `u32`s (`table_ok`), `tableZ` the zetas with
their quotients (`tableZ_ok`, `unpack`), and the tables of the code are
those of the standard (`zetaTable_eq`, `gammaTable_eq`); `saveRegs` and
`restoreRegs` keep our caller's `r4`–`r11` in memory.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem

/-! ## Barrett reduction -/

/-- `-q` as a word. -/
abbrev Nq : BitVec 32 := 4294963967

/-- The constant of `consts`. -/
def C : BitVec 32 := 161270

theorem consts_val : ((0x2 : BitVec 16) ++ ((0x75F6 : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = C := by
  decide

theorem constsN_val : ((0xFFFF : BitVec 16) ++ ((0xF2FF : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = Nq := by
  decide

/-- The low 32 bits of `X - Q · q`, computed as `Q · (2³² - q) + X`. -/
theorem sub_mul_low {X Q : Nat} (h : Q * q ≤ X) (hl : X - Q * q < 2 ^ 32) :
    (Q * 4294963967 % 2 ^ 32 + X) % 2 ^ 32 = X - Q * q := by
  rw [q_eq] at h hl ⊢
  rw [Nat.mod_add_mod, show Q * 4294963967 + X = X - Q * 3329 + Q * 2 ^ 32 by omega_using [h],
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

/-- What `barrett d t c N` leaves in `d`, with `C` in `c`. -/
def bar (x : BitVec 32) : BitVec 32 := (x >>> 11 * C) >>> 18 * Nq + x

/-- What `csubN d t N` leaves in `d`. -/
def csn (x : BitVec 32) : BitVec 32 := (x + Nq + 0x80000000) >>> 31 * Nq + x

/-- What `csub d t Q` leaves in `d`. -/
def cs (x : BitVec 32) : BitVec 32 := (x - 3329) >>> 31 * 3329 + (x - 3329)

/-- What `reduce d t c N` leaves in `d`. -/
def red (x : BitVec 32) : BitVec 32 := csn (bar x)

theorem bar_toNat {x : BitVec 32} (hx : x.toNat < 2 ^ 25) : (bar x).toNat = barrett32 x.toNat := by
  obtain ⟨b1, b2⟩ := barrett32_bounds hx
  have hT : ((x >>> 11 * C) >>> 18).toNat = barrett32Quot x.toNat := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, show C.toNat = 161270 from rfl, Nat.mod_eq_of_lt b1]
    rfl
  unfold bar barrett32
  rw [BitVec.toNat_add, BitVec.toNat_mul, hT, show Nq.toNat = 4294963967 from rfl]
  exact sub_mul_low b2 (Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt)

theorem csn_toNat {x : BitVec 32} (h : x.toNat < 2 * q) : (csn x).toNat = x.toNat % q := by
  have h' : x.toNat < 2 * 3329 := h
  have hu : ((x + Nq + 0x80000000) >>> 31).toNat = if x.toNat < 3329 then 0 else 1 := by
    split <;> bv_omega
  unfold csn
  rw [BitVec.toNat_add, BitVec.toNat_mul, hu, show Nq.toNat = 4294963967 from rfl]
  split
  · rw [sub_mul_low (by omega_arith) (by omega_using [h']), q_eq]; omega_arith
  · rw [sub_mul_low (by rw [q_eq]; omega_arith) (by omega_using [h']), q_eq]; omega_arith

theorem cs_toNat {x : BitVec 32} (h : x.toNat < 2 * q) : (cs x).toNat = x.toNat % q := by
  unfold cs
  rw [q_eq] at *
  by_cases h' : x.toNat < 3329
  · rw [Nat.mod_eq_of_lt h']; bv_omega
  · bv_omega

theorem red_toNat {x : BitVec 32} (hx : x.toNat < 2 ^ 25) : (red x).toNat = x.toNat % q := by
  unfold red
  rw [csn_toNat (by rw [bar_toNat hx]; exact barrett32_lt hx), bar_toNat hx, barrett32_mod hx]

/-! ## Products by a zeta -/

/-- `b · z - ⌊b · zetaQuot z / 2¹⁶⌋ · q`. -/
def mulzN (b z : Nat) : Nat := b * z - b * zetaQuot z / 65536 * q

theorem zetaQuot_lt {z : Nat} (hz : z < q) : zetaQuot z < 65536 := by
  unfold zetaQuot; rw [q_eq] at hz; omega_using [hz]

/-- For `b < 2¹⁶` and `z < q`: the product of `mulz` fits in 32 bits, the
multiple of `q` it subtracts is at most `b · z`, and what is left is less
than `2q`. -/
theorem mulzN_bounds {b z : Nat} (hb : b < 65536) (hz : z < q) :
    b * zetaQuot z < 2 ^ 32 ∧ b * zetaQuot z / 65536 * q ≤ b * z ∧ mulzN b z < 2 * q := by
  have hZ := zetaQuot_lt hz
  unfold mulzN
  rw [q_eq] at hz ⊢
  obtain ⟨z1, z2⟩ : zetaQuot z * 3329 ≤ z * 65536 ∧ z * 65536 + 1 ≤ zetaQuot z * 3329 + 3329 := by
    unfold zetaQuot; omega_using []
  generalize zetaQuot z = Z at *
  have pB : b * Z ≤ 65535 * 65535 := Nat.mul_le_mul (by omega_using [hb]) (by omega_using [hZ])
  have a1 : 3329 * (b * Z) ≤ 65536 * (b * z) := by
    have := Nat.mul_le_mul_left b z1
    rw [← Nat.mul_assoc, ← Nat.mul_assoc] at this
    omega_using [this]
  have a2 : 65536 * (b * z) + b ≤ 3329 * (b * Z) + 3329 * b := by
    have := Nat.mul_le_mul_left b z2
    rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_one] at this
    omega_using [this]
  generalize b * Z = A at *
  generalize b * z = X at *
  refine ⟨by omega_using [pB], by omega_using [a1], by omega_using [a1, a2, hb]⟩

theorem mulzN_mod {b z : Nat} (hb : b < 65536) (hz : z < q) : mulzN b z % q = b * z % q := by
  unfold mulzN
  rw [Nat.mul_comm (b * zetaQuot z / 65536)]
  exact Nat.sub_mul_mod (by rw [Nat.mul_comm]; exact (mulzN_bounds hb hz).2.1)

/-- What `mulz acc t z zp N` leaves in `acc`. -/
def bmz (y z zp : BitVec 32) : BitVec 32 := (y * zp) >>> 16 * Nq + y * z

theorem toNat_zq (x : Zq) : (BitVec.ofNat 32 x.val).toNat = x.val := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt x; omega_using [this])]

theorem bmz_toNat {y : BitVec 32} (hy : y.toNat < 65536) (z : Zq) :
    (bmz y (BitVec.ofNat 32 z.val) (BitVec.ofNat 32 (zetaQuot z.val))).toNat = mulzN y.toNat z.val := by
  obtain ⟨h1, h2, h3⟩ := mulzN_bounds hy z.isLt
  have hZ := zetaQuot_lt z.isLt
  have hz := val_lt z
  have eZ : (BitVec.ofNat 32 (zetaQuot z.val)).toNat = zetaQuot z.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hZ])
  have eP : ((y * BitVec.ofNat 32 (zetaQuot z.val)) >>> 16).toNat = y.toNat * zetaQuot z.val / 65536 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, eZ, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h1]
  have eX : (y * BitVec.ofNat 32 z.val).toNat = y.toNat * z.val := by
    rw [BitVec.toNat_mul, toNat_zq]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt hy hz) (by decide))
  unfold bmz
  rw [BitVec.toNat_add, BitVec.toNat_mul, eP, eX, show Nq.toNat = 4294963967 from rfl]
  exact sub_mul_low h2 (Nat.lt_of_lt_of_le h3 (by decide))

/-- For a word less than `15q`, `⌊v · 40318 / 2²⁷⌋` is `⌊v / q⌋`. -/
theorem canon_quot {v : Nat} (hv : v < 15 * q) : v * 40318 / 134217728 = v / q := by
  rw [q_eq] at *; omega_using [hv]

/-- What `canon` leaves of the word `v`. -/
def bcan (v : BitVec 32) : BitVec 32 := (v * 40318) >>> 27 * Nq + v

theorem bcan_toNat {v : BitVec 32} (hv : v.toNat < 15 * q) : (bcan v).toNat = v.toNat % q := by
  have hv' : v.toNat < 15 * 3329 := hv
  have eQ : ((v * 40318) >>> 27).toNat = v.toNat / q := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, show (40318 : BitVec 32).toNat = 40318 from rfl,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_using [hv'])]
    exact canon_quot hv
  unfold bcan
  rw [BitVec.toNat_add, BitVec.toNat_mul, eQ, show Nq.toNat = 4294963967 from rfl,
    sub_mul_low (Nat.div_mul_le_self _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) v.isLt)]
  have := Nat.div_add_mod v.toNat q
  rw [Nat.mul_comm] at this
  omega_using [this]

/-- What the inverse butterfly stores for the sum `x`. -/
def bpr (x : BitVec 32) : BitVec 32 := x >>> 12 * Nq + x

theorem bpr_toNat {x : BitVec 32} (hx : x.toNat < 4 * q) :
    (bpr x).toNat < 2 * q ∧ (bpr x).toNat % q = x.toNat % q := by
  have hx' : x.toNat < 4 * 3329 := hx
  have e : (bpr x).toNat = x.toNat - x.toNat / 4096 * q := by
    unfold bpr
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show Nq.toNat = 4294963967 from rfl]
    exact sub_mul_low (by rw [q_eq]; omega_arith) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt)
  rw [e]
  refine ⟨by rw [q_eq]; omega_using [hx'], ?_⟩
  rw [Nat.mul_comm]
  exact Nat.sub_mul_mod (by rw [q_eq]; omega_arith)

/-! ## Words -/

/-- A coefficient as the code stores it between layers. -/
abbrev Word := Fin 4294967296

/-- Words of a polynomial. -/
abbrev WPoly := Vector Word n

/-- A word, in a register. -/
abbrev wb (x : Word) : BitVec 32 := BitVec.ofNat 32 x.val

/-- A register's value, as a word. -/
abbrev toW (v : BitVec 32) : Word := Fin.ofNat _ v.toNat

/-- The residue of a word. -/
abbrev residue (x : Word) : Zq := Fin.ofNat q x.val

theorem wb_toNat (x : Word) : (wb x).toNat = x.val := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.isLt

theorem toW_val (v : BitVec 32) : (toW v).val = v.toNat := by
  rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt v.isLt

theorem wb_of {v : BitVec 32} {x : Word} (h : v.toNat = x.val) : v = wb x :=
  BitVec.eq_of_toNat_eq (by rw [wb_toNat, h])

/-- The product of the word `y` and the zeta `z`, as `mulz` leaves it. -/
abbrev bprod (y : BitVec 32) (z : Zq) : BitVec 32 :=
  bmz y (BitVec.ofNat 32 z.val) (BitVec.ofNat 32 (zetaQuot z.val))

/-! ## The forward butterfly -/

/-- What the forward butterfly stores: `x + t` and `x + 2q - t`, as words. -/
def opF (x y : Word) (z : Zq) : Word × Word :=
  (toW (wb x + bprod (wb y) z), toW (wb x + 6658 - bprod (wb y) z))

theorem opF_values (x y : Word) (z : Zq) (hx : x.val < 13 * q) (hy : y.val < 65536) :
    (opF x y z).1.val = x.val + mulzN y.val z.val ∧ (opF x y z).2.val = x.val + 2 * q - mulzN y.val z.val ∧
      mulzN y.val z.val < 2 * q ∧ mulzN y.val z.val % q = z.val * y.val % q := by
  have ht : mulzN y.val z.val < 2 * 3329 := (mulzN_bounds hy z.isLt).2.2
  have e : (bprod (wb y) z).toNat = mulzN y.val z.val := by
    have := bmz_toNat (y := wb y) (by rw [wb_toNat]; exact hy) z
    rwa [wb_toNat] at this
  have hx' := wb_toNat x
  have hx2 : x.val < 13 * 3329 := hx
  refine ⟨?_, ?_, ht, by rw [mulzN_mod hy z.isLt, Nat.mul_comm]⟩
  · simp only [opF, toW_val]
    generalize mulzN y.val z.val = P at e ht ⊢
    generalize bprod (wb y) z = T at e ⊢
    generalize wb x = X at hx' ⊢
    bv_omega
  · simp only [opF, toW_val]
    change _ = x.val + 2 * 3329 - mulzN y.val z.val
    generalize mulzN y.val z.val = P at e ht ⊢
    generalize bprod (wb y) z = T at e ⊢
    generalize wb x = X at hx' ⊢
    bv_omega

theorem opF_bound (x y : Word) (z : Zq) {b : Nat} (hb : b ≤ 13) (hx : x.val < b * q) (hy : y.val < b * q) :
    (opF x y z).1.val < (b + 2) * q ∧ (opF x y z).2.val < (b + 2) * q := by
  have hb13 : b * q ≤ 13 * q := Nat.mul_le_mul_right q hb
  have hv := opF_values x y z (Nat.lt_of_lt_of_le hx hb13)
    (Nat.lt_of_lt_of_le hy (Nat.le_trans hb13 (by decide)))
  have ht := hv.2.2.1
  rw [hv.1, hv.2.1, Nat.add_mul]
  omega_using [hx, ht]

theorem opF_residue (x y : Word) (z : Zq) (hx : x.val < 13 * q) (hy : y.val < 13 * q) :
    residue (opF x y z).1 = residue x + z * residue y ∧
    residue (opF x y z).2 = residue x - z * residue y := by
  have hv := opF_values x y z hx (Nat.lt_of_lt_of_le hy (by decide))
  generalize mulzN y.val z.val = P at hv
  obtain ⟨v1, v2, ht, hm⟩ := hv
  have hm' : (z * residue y).val = P % q := by
    rw [Fin.val_mul, residue, Fin.val_ofNat, Nat.mul_mod_mod, hm]
  constructor
  · apply Fin.ext
    rw [Fin.val_add, hm']
    change (opF x y z).1.val % q = (x.val % q + P % q) % q
    rw [v1, Nat.add_mod]
  · apply Fin.ext
    rw [Fin.val_sub, hm']
    change (opF x y z).2.val % q = (q - P % q + x.val % q) % q
    rw [v2]
    have ht' : P < 2 * 3329 := ht
    change (x.val + 2 * 3329 - P) % 3329 = (3329 - P % 3329 + x.val % 3329) % 3329
    omega_using [ht']

/-! ## The inverse butterfly -/

/-- What the inverse butterfly stores: `x + y` less a multiple of `q`, and
the product of the zeta and `y + 2q - x`, as words. -/
def opI (x y : Word) (z : Zq) : Word × Word :=
  (toW (bpr (wb x + wb y)), toW (bprod (wb y + 6658 - wb x) z))

theorem opI_values (x y : Word) (z : Zq) (hx : x.val < 2 * q) (hy : y.val < 2 * q) :
    (opI x y z).1.val < 2 * q ∧ (opI x y z).1.val % q = (x.val + y.val) % q ∧
      (opI x y z).2.val < 2 * q ∧ (opI x y z).2.val % q = z.val * (y.val + 2 * q - x.val) % q := by
  have hx' := wb_toNat x
  have hy' := wb_toNat y
  have hx2 : x.val < 2 * 3329 := hx
  have hy2 : y.val < 2 * 3329 := hy
  have hs : (wb x + wb y).toNat = x.val + y.val := by
    generalize wb x = X at hx' ⊢
    generalize wb y = Y at hy' ⊢
    bv_omega
  have hd : (wb y + 6658 - wb x).toNat = y.val + 2 * q - x.val := by
    rw [q_eq]
    generalize wb x = X at hx' ⊢
    generalize wb y = Y at hy' ⊢
    bv_omega
  have hlt : y.val + 2 * q - x.val < 65536 := by rw [q_eq]; omega_using [hy2]
  obtain ⟨p1, p2⟩ := bpr_toNat (x := wb x + wb y) (by rw [hs, q_eq]; omega_using [hx2, hy2])
  have e : (bprod (wb y + 6658 - wb x) z).toNat = mulzN (wb y + 6658 - wb x).toNat z.val :=
    bmz_toNat (y := wb y + 6658 - wb x) (by rw [hd]; exact hlt) z
  simp only [opI, toW_val]
  refine ⟨p1, by rw [p2, hs], ?_, ?_⟩
  · rw [e, hd]; exact (mulzN_bounds hlt z.isLt).2.2
  · rw [e, hd, mulzN_mod hlt z.isLt, Nat.mul_comm]

theorem opI_residue (x y : Word) (z : Zq) (hx : x.val < 2 * q) (hy : y.val < 2 * q) :
    residue (opI x y z).1 = residue x + residue y ∧
    residue (opI x y z).2 = z * (residue y - residue x) := by
  obtain ⟨-, v1, -, v2⟩ := opI_values x y z hx hy
  constructor
  · apply Fin.ext
    rw [Fin.val_add]
    change (opI x y z).1.val % q = (x.val % q + y.val % q) % q
    rw [v1, Nat.add_mod]
  · apply Fin.ext
    change (opI x y z).2.val % q = (z * (residue y - residue x)).val
    rw [v2, Fin.val_mul, Fin.val_sub, residue, residue, Fin.val_ofNat, Fin.val_ofNat]
    have hl : (y.val + 2 * q - x.val) % q = (q - x.val % q + y.val % q) % q := by
      rw [q_eq] at hx hy ⊢; omega_using [hx]
    rw [Nat.mul_mod, hl, Nat.mul_mod z.val ((q - x.val % q + y.val % q) % q), Nat.mod_mod]

/-! ## Layers -/

/-- Words bounded by `b q` whose residues are `f`'s. -/
def Rel (b : Nat) (F : WPoly) (f : Poly) : Prop :=
  ∀ i < 256, F[i]!.val < b * q ∧ residue F[i]! = f[i]!

/-- A polynomial's coefficients as words. -/
def lift (f : Poly) : WPoly := f.map fun x => ⟨x.val, Nat.lt_trans (val_lt x) (by decide)⟩

theorem lift_get (f : Poly) {i : Nat} (hi : i < 256) : ((lift f)[i]!).val = (f[i]!).val := by
  rw [getElem!_pos (lift f) i hi, lift, Vector.getElem_map, getElem!_pos f i hi]

theorem lift_rel (f : Poly) : Rel 1 (lift f) f := by
  intro i hi
  have he := lift_get f hi
  refine ⟨by rw [he, Nat.one_mul]; exact f[i]!.isLt, Fin.ext ?_⟩
  rw [Fin.val_ofNat, he]; exact Nat.mod_eq_of_lt f[i]!.isLt

theorem Rel.mono {b b' : Nat} (h : b ≤ b') {F : WPoly} {f : Poly} (hF : Rel b F f) : Rel b' F f :=
  fun i hi => ⟨Nat.lt_of_lt_of_le (hF i hi).1 (Nat.mul_le_mul_right q h), (hF i hi).2⟩

/-- A layer of the forward butterflies on words. -/
def layerF (F : WPoly) (len : Nat) : WPoly := layF (wBlockN opF) F len (fun c => 128 / len + c) (128 / len)

/-- A layer of the inverse butterflies on words. -/
def layerI (F : WPoly) (len : Nat) : WPoly :=
  layF (wBlockN opI) F len (fun c => 256 / len - 1 - c) (128 / len)

theorem len_facts {len : Nat} (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128]) :
    0 < len ∧ 2 * len * (128 / len) = 256 ∧
      ∀ i < 256, (i % (2 * len) < len → i + len < 256) ∧ (¬ i % (2 * len) < len → len ≤ i) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
  rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨by decide, by decide, ?_⟩
  all_goals intro i hi; omega_using [hi]

theorem layerF_rel {b : Nat} (hb : b ≤ 13) {F : WPoly} {f : Poly} (hF : Rel b F f)
    {len : Nat} (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128]) :
    Rel (b + 2) (layerF F len) (nttLayer f len) := by
  have hl := len_facts hlen
  have lt : ∀ {x : Word}, x.val < b * q → x.val < 13 * q := fun h =>
    Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right q hb)
  intro i hi
  rw [layerF, layF_get (wBlk_ok opF) F hl.1 _ (by omega) hi, nttLayer_get f hl.1 hl.2.1 hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    exact ⟨(opF_bound _ _ _ hb h0.1 h1.1).1, by rw [(opF_residue _ _ _ (lt h0.1) (lt h1.1)).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega_using [hi])
    have h1 := hF i hi
    exact ⟨(opF_bound _ _ _ hb h0.1 h1.1).2, by rw [(opF_residue _ _ _ (lt h0.1) (lt h1.1)).2, h0.2, h1.2]⟩

theorem layerI_rel {F : WPoly} {f : Poly} (hF : Rel 2 F f) {len : Nat}
    (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128]) : Rel 2 (layerI F len) (nttInvLayer f len) := by
  have hl := len_facts hlen
  intro i hi
  rw [layerI, layF_get (wBlk_ok opI) F hl.1 _ (by omega) hi, nttInvLayer_get f hl.1 hl.2.1 hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    exact ⟨(opI_values _ _ _ h0.1 h1.1).1, by rw [(opI_residue _ _ _ h0.1 h1.1).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega_using [hi])
    have h1 := hF i hi
    exact ⟨(opI_values _ _ _ h0.1 h1.1).2.2.1, by rw [(opI_residue _ _ _ h0.1 h1.1).2, h0.2, h1.2]⟩

/-- The layers `ls` of `NTT`, from words less than `b q`. -/
theorem layersF_rel : ∀ (ls : List Nat) (b : Nat) (F : WPoly) (f : Poly),
    (∀ len ∈ ls, len ∈ [2, 4, 8, 16, 32, 64, 128]) → b + 2 * ls.length ≤ 15 → Rel b F f →
    Rel (b + 2 * ls.length) (ls.foldl layerF F) (ls.foldl nttLayer f)
  | [], _, _, _, _, _, h => h
  | len :: ls, b, F, f, hls, hb, h => by
    rw [List.length_cons] at hb
    have := layersF_rel ls (b + 2) (layerF F len) (nttLayer f len) (fun l hl => hls l (List.mem_cons_of_mem _ hl))
      (by omega_using [hb]) (layerF_rel (by omega_using [hb]) h (hls len (List.mem_cons_self ..)))
    rw [List.length_cons, show b + 2 * (ls.length + 1) = b + 2 + 2 * ls.length by omega_arith]
    exact this

/-- The layers `ls` of `NTT⁻¹`, from words less than `2q`. -/
theorem layersI_rel : ∀ (ls : List Nat) (F : WPoly) (f : Poly), (∀ len ∈ ls, len ∈ [2, 4, 8, 16, 32, 64, 128]) →
    Rel 2 F f → Rel 2 (ls.foldl layerI F) (ls.foldl nttInvLayer f)
  | [], _, _, _, h => h
  | len :: ls, F, f, hls, h =>
    layersI_rel ls (layerI F len) (nttInvLayer f len) (fun l hl => hls l (List.mem_cons_of_mem _ hl))
      (layerI_rel h (hls len (List.mem_cons_self ..)))

/-! ## The last layers -/

/-- What a butterfly of the last layer of `NTT` stores: `opF`, reduced. -/
def opFC (x y : Word) (z : Zq) : Word × Word :=
  (toW (bcan (wb x + bprod (wb y) z)), toW (bcan (wb x + 6658 - bprod (wb y) z)))

theorem opFC_val (x y : Word) (z : Zq) (hx : x.val < 13 * q) (hy : y.val < 13 * q) :
    (opFC x y z).1.val = (residue (opF x y z).1).val ∧ (opFC x y z).2.val = (residue (opF x y z).2).val := by
  have hb := opF_bound x y z (Nat.le_refl 13) hx hy
  constructor
  · show (toW (bcan (wb x + bprod (wb y) z))).val = _
    rw [toW_val, bcan_toNat (by rw [← toW_val]; exact hb.1), Fin.val_ofNat]
    exact congrArg (· % q) (toW_val _).symm
  · show (toW (bcan (wb x + 6658 - bprod (wb y) z))).val = _
    rw [toW_val, bcan_toNat (by rw [← toW_val]; exact hb.2), Fin.val_ofNat]
    exact congrArg (· % q) (toW_val _).symm

/-- The last layer of `NTT` on words. -/
def layerFC (F : WPoly) (len : Nat) : WPoly := layF (wBlockN opFC) F len (fun c => 128 / len + c) (128 / len)

/-- The last layer of `NTT` leaves the specification's coefficients. -/
theorem layerFC_val {F : WPoly} {f : Poly} (hF : Rel 13 F f) {len : Nat}
    (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128]) {i : Nat} (hi : i < 256) :
    ((layerFC F len)[i]!).val = ((nttLayer f len)[i]!).val := by
  have hl := len_facts hlen
  rw [layerFC, layF_get (wBlk_ok opFC) F hl.1 _ (by omega) hi, nttLayer_get f hl.1 hl.2.1 hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    rw [(opFC_val _ _ _ h0.1 h1.1).1, (opF_residue _ _ _ h0.1 h1.1).1, h0.2, h1.2]
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega_using [hi])
    have h1 := hF i hi
    rw [(opFC_val _ _ _ h0.1 h1.1).2, (opF_residue _ _ _ h0.1 h1.1).2, h0.2, h1.2]

/-- The multiplier of the last step of `NTT⁻¹`. -/
abbrev cInv : Zq := 3303

/-- A word less than `2¹⁶` times a zeta, reduced. -/
theorem scale_val {v : BitVec 32} {x : Word} (hv : v.toNat = x.val) (hx : x.val < 65536) (z : Zq) :
    (cs (bprod v z)).toNat = (residue x * z).val := by
  have hlt : v.toNat < 65536 := by rw [hv]; exact hx
  rw [cs_toNat (by rw [bmz_toNat hlt]; exact (mulzN_bounds hlt z.isLt).2.2), bmz_toNat hlt,
    mulzN_mod hlt z.isLt, hv, Fin.val_mul, Fin.val_ofNat, Nat.mod_mul_mod]

/-- What a butterfly of the last layer of `NTT⁻¹` stores: the sum times
3303, and the difference times the zeta and 3303, reduced. -/
def opIS (x y : Word) (z : Zq) : Word × Word :=
  (toW (cs (bprod (wb x + wb y) cInv)), toW (cs (bprod (wb y + 6658 - wb x) (z * cInv))))

theorem opIS_val (x y : Word) (z : Zq) (hx : x.val < 2 * q) (hy : y.val < 2 * q) :
    (opIS x y z).1.val = ((residue x + residue y) * cInv).val ∧
    (opIS x y z).2.val = ((residue y - residue x) * (z * cInv)).val := by
  have hx' := wb_toNat x
  have hy' := wb_toNat y
  have hx2 : x.val < 2 * 3329 := hx
  have hy2 : y.val < 2 * 3329 := hy
  have hs : (wb x + wb y).toNat = x.val + y.val := by
    generalize wb x = X at hx' ⊢
    generalize wb y = Y at hy' ⊢
    bv_omega
  have hd : (wb y + 6658 - wb x).toNat = y.val + 2 * 3329 - x.val := by
    generalize wb x = X at hx' ⊢
    generalize wb y = Y at hy' ⊢
    bv_omega
  have es : residue (toW (wb x + wb y)) = residue x + residue y := by
    apply Fin.ext
    rw [Fin.val_add]
    show (toW (wb x + wb y)).val % 3329 = (x.val % 3329 + y.val % 3329) % 3329
    rw [toW_val, hs]
    omega_using []
  have ed : residue (toW (wb y + 6658 - wb x)) = residue y - residue x := by
    apply Fin.ext
    rw [Fin.val_sub]
    show (toW (wb y + 6658 - wb x)).val % 3329 = (3329 - x.val % 3329 + y.val % 3329) % 3329
    rw [toW_val, hd]
    omega_using [hx2]
  constructor
  · show (toW (cs (bprod (wb x + wb y) cInv))).val = _
    rw [toW_val, scale_val (toW_val _).symm (by rw [toW_val, hs]; omega_using [hx2, hy2]) cInv, es]
  · show (toW (cs (bprod (wb y + 6658 - wb x) (z * cInv)))).val = _
    rw [toW_val, scale_val (toW_val _).symm (by rw [toW_val, hd]; omega_using [hy2]) (z * cInv), ed]

/-- The last layer of `NTT⁻¹` multiplies the difference by the zeta, and the
result by 3303. -/
theorem mul_scale (x z c : Zq) : x * (z * c) = z * x * c := by
  rw [← Fin.mul_assoc, Fin.mul_comm x z]

/-- The last layer of `NTT⁻¹` and the multiplication by 3303 leave the
specification's coefficients. -/
theorem lastInv_val {F : WPoly} {f : Poly} (hF : Rel 2 F f) {i : Nat} (hi : i < 256) :
    ((wBlockN opIS F 128 1 0 128)[i]!).val = (((nttInvLayer f 128).map (· * 3303))[i]!).val := by
  rw [wBlockN_get opIS F (by decide) (Nat.le_refl _) (by decide) hi, map_mul_get _ (by rw [n_eq]; exact hi),
    nttInvLayer_get f (by decide) (by decide) hi]
  by_cases h : i < 128
  · have h0 := hF i hi
    have h1 := hF (i + 128) (by omega_using [h])
    rw [ite_eq_left (show 0 ≤ i ∧ i < 0 + 128 from ⟨Nat.zero_le _, by omega_using [h]⟩),
      ite_eq_left (show i % (2 * 128) < 128 by omega_using [h]), (opIS_val _ _ _ h0.1 h1.1).1, h0.2, h1.2]
  · have h0 := hF (i - 128) (by omega_using [hi])
    have h1 := hF i hi
    rw [ite_eq_right (show ¬ (0 ≤ i ∧ i < 0 + 128) from fun e => h (by omega_using [e.2])),
      ite_eq_left (show 0 + 128 ≤ i ∧ i < 0 + 128 + 128 from ⟨by omega_using [h], by omega_using [hi]⟩),
      ite_eq_right (show ¬ i % (2 * 128) < 128 by omega_using [h, hi]), (opIS_val _ _ _ h0.1 h1.1).2, h0.2, h1.2,
      show 256 / 128 - 1 - i / (2 * 128) = 1 by omega_using [hi], mul_scale]

/-! ## Words in memory -/

/-- The words of `W` stored at `p`. -/
def LP (m : Mem) (p : Addr) (W : WPoly) : Prop := ∀ i < n, (coeffAt m p i).toNat = W[i]!.val

theorem lp_lift {m : Mem} {p : Addr} {f : Poly} (h : PolyIs m p f) : LP m p (lift f) := fun i hi => by
  rw [polyIs_toNat h hi, lift_get f (by rw [n_eq] at hi; exact hi)]

/-- The word stored for a coefficient. -/
theorem lp_word {m : Mem} {P : Addr} {W : WPoly} (h : LP m P W) {j : Nat} (hj : j < n) :
    m.readW (coeffAddr P j) 32 = wb W[j]! := by
  rw [← coeffAt_eq]; exact wb_of (h j hj)

/-- A butterfly's two stores: `f[j + len]`, then `f[j]`. -/
theorem lp_bfly {m : Mem} {F : Addr} {W : WPoly} (h : LP m F W) (op : Word → Word → Zq → Word × Word)
    {j len : Nat} (hl : 0 < len) (hj : j + len < n) (z : Zq) {v₁ v₂ : BitVec 32}
    (h₁ : v₁.toNat = (op W[j]! W[j + len]! z).1.val) (h₂ : v₂.toNat = (op W[j]! W[j + len]! z).2.val) :
    LP ((m.writeW (coeffAddr F (j + len)) v₂).writeW (coeffAddr F j) v₁) F (wbfly op W j len z) := by
  intro i hi
  rw [coeffAt_writeW _ _ hi (by omega_using [hj]), coeffAt_writeW _ _ hi hj, wbfly_get op W hl hj z hi]
  rcases (by omega_using [] : i = j ∨ i = j + len ∨ (i ≠ j ∧ i ≠ j + len)) with rfl | rfl | ⟨a, b⟩
  · rw [ite_eq_left rfl, ite_eq_left rfl]; exact h₁
  · rw [ite_eq_right (by omega_using [hl]), ite_eq_left rfl, ite_eq_right (by omega_using [hl]), ite_eq_left rfl]
    exact h₂
  · rw [ite_eq_right (Ne.symm a), ite_eq_right (Ne.symm b), ite_eq_right a, ite_eq_right b]; exact h i hi

/-- An inverse butterfly's two stores: `f[j]`, then `f[j + len]`. -/
theorem lp_bflyInv {m : Mem} {F : Addr} {W : WPoly} (h : LP m F W) (op : Word → Word → Zq → Word × Word)
    {j len : Nat} (hl : 0 < len) (hj : j + len < n) (z : Zq) {v₁ v₂ : BitVec 32}
    (h₁ : v₁.toNat = (op W[j]! W[j + len]! z).1.val) (h₂ : v₂.toNat = (op W[j]! W[j + len]! z).2.val) :
    LP ((m.writeW (coeffAddr F j) v₁).writeW (coeffAddr F (j + len)) v₂) F (wbfly op W j len z) := by
  intro i hi
  rw [coeffAt_writeW _ _ hi hj, coeffAt_writeW _ _ hi (by omega_using [hj]), wbfly_get op W hl hj z hi]
  rcases (by omega_using [] : i = j ∨ i = j + len ∨ (i ≠ j ∧ i ≠ j + len)) with rfl | rfl | ⟨a, b⟩
  · rw [ite_eq_right (by omega_using [hl]), ite_eq_left rfl, ite_eq_left rfl]; exact h₁
  · rw [ite_eq_left rfl, ite_eq_right (by omega_using [hl]), ite_eq_left rfl]; exact h₂
  · rw [ite_eq_right (Ne.symm b), ite_eq_right (Ne.symm a), ite_eq_right a, ite_eq_right b]; exact h i hi

/-! ## Tables -/

theorem zetaTable_eq : zetaTable = zetas := rfl

theorem gammaTable_eq : gammaTable = gammas := rfl

/-- An entry of a table, as `movw` builds it. -/
theorem movw_val {v : Nat} (hv : v < 65536) : (BitVec.ofNat 16 v).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (by omega_using [hv])]

/-- After the first `k` entries of a table at `b`. -/
structure TabInv (T : List Nat) (b : Reg) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr b), 512⟩] s₀.mem s.mem
  tab : ∀ j < k, s.mem.readW (State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * j)) 32 =
    BitVec.ofNat 32 (T.getD j 0)

theorem tab_step {s : State} {b : Reg} {B : BitVec 32} {k : Nat} (hk : 4 * k < 4096) (hb : s.gpr b = B)
    (hin : InRegions s.wr (State.addr (B + BitVec.ofNat 32 (4 * k))) 4) (v : BitVec 16) (hbr : b ≠ .r12) :
    WP isa (.block [.movw .r12 v, .str .r12 b (4 * k)]) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW (State.addr (B + BitVec.ofNat 32 (4 * k))) (v.setWidth 32) := by
  have ho : 4 * k < 4096 := hk
  run_block [hb, hbr, hin, ho, ite_false, implies_true]
  exact ⟨fun r hr => ite_eq_right hr, trivial⟩

/-- `table T b` stores the table `T` at `b`. -/
theorem table_ok (T : List Nat) (hT : ∀ k < 128, T.getD k 0 < 65536) {b : Reg} (hb : b ≠ .r12)
    {s₀ : State} (hfit : (s₀.gpr b).toNat + 512 ≤ 2 ^ 32)
    (hwr : ∀ k < 128, InRegions s₀.wr (State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (table T b)) s₀ (TabInv T b s₀ 128) := by
  refine wp_range_flatMap (M := isa) (TabInv T b s₀) (fun k s hk h => ?_) 128 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s₀.gpr b + BitVec.ofNat 32 (4 * k)) = State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * k) :=
    addr_add (by omega_using [hfit, hk])
  refine WP.mono (tab_step (k := k) (by omega_using [hk]) (h.gpr b hb) (by rw [ea, h.wr]; exact hwr k hk) _ hb)
    fun s' ⟨g, rd, wr, sp, m⟩ => ⟨fun r hr => (g r hr).trans (h.gpr r hr), rd.trans h.rd, wr.trans h.wr,
      sp.trans h.sp, ?_, fun j hj => ?_⟩
  · rw [m, ea]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega_using [hk]) (by omega_using [hk]))
  · rw [m, ea, movw_val (hT k hk)]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [e]) (by omega_using [hk, hj]) (by omega_using [hk])) (by decide)]
      exact h.tab j (by omega_using [hj, e])

/-- A zeta with its quotient, as `movw` and `movt` build the word. -/
theorem movwt_val (z : Nat) {zp : Nat} (hzp : zp < 65536) :
    (BitVec.ofNat 16 z ++ ((BitVec.ofNat 16 zp).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 (zp + 65536 * z) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_zero, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega_using [])]
  omega_using [hzp]

/-- What `zetaLoad` leaves in `r7` and `r9`, of the word of a zeta and its
quotient. -/
theorem unpack {z zp : Nat} (hz : z < 65536) (hzp : zp < 65536) :
    BitVec.ofNat 32 (zp + 65536 * z) >>> 16 = BitVec.ofNat 32 z ∧
      BitVec.ofNat 32 (zp + 65536 * z) - (BitVec.ofNat 32 (zp + 65536 * z) >>> 16) <<< 16 = BitVec.ofNat 32 zp := by
  have e : (BitVec.ofNat 32 (zp + 65536 * z)).toNat = zp + 65536 * z := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hz, hzp])
  have e1 : (BitVec.ofNat 32 z).toNat = z := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hz])
  have e2 : (BitVec.ofNat 32 zp).toNat = zp := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hzp])
  generalize BitVec.ofNat 32 (zp + 65536 * z) = W at e ⊢
  generalize BitVec.ofNat 32 z = Z at e1 ⊢
  generalize BitVec.ofNat 32 zp = P at e2 ⊢
  constructor <;> bv_omega

/-- After the first `k` entries of a table of zetas at `b`. -/
structure TabZInv (T : List Nat) (b : Reg) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr b), 512⟩] s₀.mem s.mem
  tab : ∀ j < k, s.mem.readW (State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * j)) 32 =
    BitVec.ofNat 32 (zetaQuot (T.getD j 0) + 65536 * T.getD j 0)

theorem tabZ_step {s : State} {b : Reg} {B : BitVec 32} {k : Nat} (hk : 4 * k < 4096) (hb : s.gpr b = B)
    (hin : InRegions s.wr (State.addr (B + BitVec.ofNat 32 (4 * k))) 4) (v w : BitVec 16) (hbr : b ≠ .r12) :
    WP isa (.block [.movw .r12 v, .movt .r12 w, .str .r12 b (4 * k)]) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW (State.addr (B + BitVec.ofNat 32 (4 * k)))
        (w ++ (v.setWidth 32).extractLsb' 0 16 : BitVec 32) := by
  have ho : 4 * k < 4096 := hk
  run_block [hb, hbr, hin, ho, ite_false, implies_true]
  exact ⟨fun r hr => by rw [ite_eq_right hr, ite_eq_right hr], trivial⟩

/-- `tableZ T b` stores the zetas `T`, each with its quotient, at `b`. -/
theorem tableZ_ok (T : List Nat) (hT : ∀ k < 128, T.getD k 0 < 3329) {b : Reg} (hb : b ≠ .r12)
    {s₀ : State} (hfit : (s₀.gpr b).toNat + 512 ≤ 2 ^ 32)
    (hwr : ∀ k < 128, InRegions s₀.wr (State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (tableZ T b)) s₀ (TabZInv T b s₀ 128) := by
  refine wp_range_flatMap (M := isa) (TabZInv T b s₀) (fun k s hk h => ?_) 128 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s₀.gpr b + BitVec.ofNat 32 (4 * k)) = State.addr (s₀.gpr b) + BitVec.ofNat 64 (4 * k) :=
    addr_add (by omega_using [hfit, hk])
  refine WP.mono (tabZ_step (k := k) (by omega_using [hk]) (h.gpr b hb) (by rw [ea, h.wr]; exact hwr k hk) _ _ hb)
    fun s' ⟨g, rd, wr, sp, m⟩ => ⟨fun r hr => (g r hr).trans (h.gpr r hr), rd.trans h.rd, wr.trans h.wr,
      sp.trans h.sp, ?_, fun j hj => ?_⟩
  · rw [m, ea]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega_using [hk]) (by omega_using [hk]))
  · rw [m, ea, movwt_val _ (zetaQuot_lt (hT k hk))]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [e]) (by omega_using [hk, hj]) (by omega_using [hk])) (by decide)]
      exact h.tab j (by omega_using [hj, e])

/-! ## Regions at offsets from a base -/

theorem region_sub_off {S : Addr} {o n len : Nat} (h : o + n ≤ len) :
    Region.Sub ⟨S + BitVec.ofNat 64 o, n⟩ ⟨S, len⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  bv_omega

theorem region_disj_off {S : Addr} {o₁ n₁ o₂ n₂ L : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁)
    (h₁ : o₁ + n₁ ≤ L) (h₂ : o₂ + n₂ ≤ L) (hS : S.toNat + L ≤ 2 ^ 64) :
    Region.Disjoint ⟨S + BitVec.ofNat 64 o₁, n₁⟩ ⟨S + BitVec.ofNat 64 o₂, n₂⟩ := by
  intro a ha hb
  simp only [Region.Contains] at ha hb
  bv_omega

theorem add_ofNat_zero (S : Addr) : S + BitVec.ofNat 64 0 = S := by simp

theorem add_ofNat_add (S : Addr) (a b : Nat) :
    S + BitVec.ofNat 64 a + BitVec.ofNat 64 b = S + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ptr_add_add32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem addr_toNat64 (a : BitVec 32) : (State.addr a).toNat + 2 ^ 32 ≤ 2 ^ 64 := by
  rw [addr_toNat]; have := a.isLt; omega_using []

/-- A pointer to `L ≤ 2³²` bytes, as a 64-bit address, does not wrap around. -/
theorem addr_fit (a : BitVec 32) {L : Nat} (hL : L ≤ 2 ^ 32) : (State.addr a).toNat + L ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.add_le_add_left hL _) (addr_toNat64 a)

theorem fit_le {a : BitVec 32} {k L : Nat} (hk : k ≤ L) (h : a.toNat + L ≤ 2 ^ 32) : a.toNat + k ≤ 2 ^ 32 :=
  Nat.le_trans (Nat.add_le_add_left hk _) h

/-! ## Saved registers -/

theorem savedRegs_nodup : ∀ i < 8, ∀ j < 8, savedRegs.getD i .r4 = savedRegs.getD j .r4 → i = j := by
  decide

theorem savedRegs_mem : ∀ i < 8, savedRegs.getD i .r4 ∈ savedRegs := by decide

/-- The registers `g` saved at `A`. -/
def Saved (m : Mem) (A : Addr) (g : Reg → BitVec 32) : Prop :=
  ∀ i < 8, m.readW (A + BitVec.ofNat 64 (4 * i)) 32 = g (savedRegs.getD i .r4)

/-- After saving the first `k` registers at `A = b + off`. -/
structure SaveInv (b : Reg) (off : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr b) + BitVec.ofNat 64 off, 32⟩] s₀.mem s.mem
  saved : ∀ i < k, s.mem.readW (State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * i)) 32 =
    s₀.gpr (savedRegs.getD i .r4)

theorem saveRegs_ok (b : Reg) {off : Nat} (ho : off + 28 < 4096) {s₀ : State}
    (hfit : (s₀.gpr b).toNat + (off + 32) ≤ 2 ^ 32)
    (hwr : ∀ i < 8, InRegions s₀.wr (State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (saveRegs b off)) s₀ (SaveInv b off s₀ 8) := by
  refine wp_range_flatMap (M := isa) (SaveInv b off s₀) (fun k s hk h => ?_) 8 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s.gpr b + BitVec.ofNat 32 (off + 4 * k)) =
      State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * k) := by
    rw [h.gpr, addr_add (by omega_using [hfit, hk]), BitVec.add_assoc, ← BitVec.ofNat_add]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_str (by omega_using [ho, hk]) (by rw [ea, h.wr]; exact hwr k hk), runStep_some, runBlock_nil]
  refine ⟨_, rfl, h.gpr, h.rd, h.wr, h.sp, ?_, fun j hj => ?_⟩
  · rw [ea]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega_using [hk]) (by omega_using [hk]))
  · show (s.mem.writeW _ _).readW _ _ = _
    rw [ea, h.gpr]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [e]) (by omega_using [hk, hj]) (by omega_using [hk])) (by decide)]
      exact h.saved j (by omega_using [hj, e])

/-- After loading the first `k` registers from `A = b + off`. -/
structure RestoreInv (g : Reg → BitVec 32) (s₀ : State) (k : Nat) (s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  other : ∀ r, r ∉ savedRegs → s.gpr r = s₀.gpr r
  loaded : ∀ i < k, s.gpr (savedRegs.getD i .r4) = g (savedRegs.getD i .r4)

theorem restoreRegs_ok (b : Reg) (hb : b ∉ savedRegs) {off : Nat} (ho : off + 28 < 4096) {s₀ : State}
    (hfit : (s₀.gpr b).toNat + (off + 32) ≤ 2 ^ 32) {g : Reg → BitVec 32}
    (hs : Saved s₀.mem (State.addr (s₀.gpr b) + BitVec.ofNat 64 off) g)
    (hrd : ∀ i < 8, InRegions (s₀.rd ++ s₀.wr)
      (State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (restoreRegs b off)) s₀ (RestoreInv g s₀ 8) := by
  refine wp_range_flatMap (M := isa) (RestoreInv g s₀) (fun k s hk h => ?_) 8 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : State.addr (s.gpr b + BitVec.ofNat 32 (off + 4 * k)) =
      State.addr (s₀.gpr b) + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * k) := by
    rw [h.other b hb, addr_add (by omega_using [hfit, hk]), BitVec.add_assoc, ← BitVec.ofNat_add]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_ldr (by omega_using [ho, hk]) (by rw [ea, h.rd, h.wr]; exact hrd k hk), runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, h.mem, h.rd, h.wr, h.sp, fun r hr => ?_, fun j hj => ?_⟩
  · show (s.setReg _ _).gpr r = _
    simp only [State.setReg]
    rw [ite_eq_right (fun (e : r = savedRegs.getD k .r4) => hr (e ▸ savedRegs_mem k hk)), h.other r hr]
  · show (s.setReg _ _).gpr _ = _
    simp only [State.setReg]
    by_cases e : j = k
    · subst e; rw [ite_eq_left rfl, ea, h.mem]; exact hs j hk
    · rw [ite_eq_right (fun e' => e (savedRegs_nodup j (by omega_using [hk, hj]) k hk e'))]
      exact h.loaded j (by omega_using [hj, e])

/-- The callee-saved registers, restored. -/
theorem preserved_of_restore {g : Reg → BitVec 32} {s₀ s : State} (h : RestoreInv g s₀ 8 s)
    (hlr : s₀.gpr .lr = g .lr) : ∀ r ∈ preserved, s.gpr r = g r := by
  have : ∀ r ∈ preserved, r = .lr ∨ ∃ i < 8, savedRegs.getD i .r4 = r := by decide
  intro r hr
  rcases this r hr with rfl | ⟨i, hi, rfl⟩
  · rw [h.other .lr (by decide), hlr]
  · exact h.loaded i hi

end VG.Proof.MlKem.Arm
