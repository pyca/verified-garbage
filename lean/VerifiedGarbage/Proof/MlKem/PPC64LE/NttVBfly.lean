module

-- separate module: its proofs (about 10 s) build in parallel with `Reduce`'s, which `Ntt` also imports

public import VerifiedGarbage.Proof.Framework.PPC64LE.VWords
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Ntt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlKem.NttLayer
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on PPC64LE: the vector NTT, word by word

What `Proof/MlKem/PPC64LE/Ntt.lean` needs of the vector NTT's code
(`Impl/MlKem/PPC64LE/Ntt.lean`) but its loops, on the words of vectors of
`Proof/Framework/PPC64LE/VWords.lean`:

* the butterflies of `vbfly` on each word (`vbfly_ok`): from coefficients
  `x`, `y` below `q` and a zeta `z` below `q` with `z' = ⌊z · 2³² / q⌋`
  (`zetaPrime`), the words of `v6` and `v7` become `(x + z·y) mod q` and
  `(x - z·y) mod q`. The product by the zeta is Shoup's (`shoup_bounds`):
  `y·z - ⌊y·z' / 2³²⌋·q` is less than `2q`, and `min(v, v - q)` of a word
  below `2q` is its remainder (`minq`);
* rows of four coefficients loaded and stored (`row_lane`, `coeffAt_row`,
  `polyIs_rows`);
* the bodies of the inner loop (`body_ok`), four butterflies of a block
  (`group_poly`), and of the last layer (`body2_ok`), two blocks of
  `len = 2` (`pair_poly`).
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.VBfly

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE

/-! ## Arithmetic -/

theorem shoup_bounds {a z q D : Nat} (hq : 0 < q) (hD : 0 < D) (ha : a < D) :
    a * (z * D / q) / D * q ≤ a * z ∧ a * z < a * (z * D / q) / D * q + 2 * q := by
  generalize hz' : z * D / q = z' at *
  generalize ht : a * z' / D = t
  have e1 : z' * q ≤ z * D := hz' ▸ Nat.div_mul_le_self _ _
  have e2 : z * D < (z' + 1) * q := by
    rw [← hz', Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add hq
  have e3 : t * D ≤ a * z' := ht ▸ Nat.div_mul_le_self _ _
  have e4 : a * z' < (t + 1) * D := by
    rw [← ht, Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add hD
  constructor
  · apply Nat.le_of_mul_le_mul_right (c := D) _ hD
    calc t * q * D = t * D * q := by rw [Nat.mul_right_comm]
      _ ≤ a * z' * q := Nat.mul_le_mul_right _ e3
      _ = a * (z' * q) := by rw [Nat.mul_assoc]
      _ ≤ a * (z * D) := Nat.mul_le_mul_left _ e1
      _ = a * z * D := by rw [Nat.mul_assoc]
  · apply Nat.lt_of_mul_lt_mul_right (a := D)
    calc a * z * D = a * (z * D) := by rw [Nat.mul_assoc]
      _ ≤ a * ((z' + 1) * q) := Nat.mul_le_mul_left _ (Nat.le_of_lt e2)
      _ = a * z' * q + a * q := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_assoc]
      _ < (t + 1) * D * q + D * q :=
          Nat.add_lt_add (Nat.mul_lt_mul_of_pos_right e4 hq) (Nat.mul_lt_mul_of_pos_right ha hq)
      _ = (t * q + 2 * q) * D := by grind

abbrev Q32 : BitVec 32 := 3329

theorem toNat_sub_q (v : BitVec 32) : (v - Q32).toNat = (v.toNat + (2 ^ 32 - 3329)) % 2 ^ 32 := by
  rw [BitVec.toNat_sub, show Q32.toNat = 3329 from rfl]; omega

/-- `min(v, v - q)` of a word below `2q` is its remainder mod `q`. -/
theorem minq {v : BitVec 32} (hv : v.toNat < 2 * 3329) :
    (if v.toNat < (v - Q32).toNat then v else v - Q32) = BitVec.ofNat 32 (v.toNat % 3329) := by
  have hs := toNat_sub_q v
  split
  · rename_i h
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; rw [hs] at h; omega
  · rename_i h
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, hs]; rw [hs] at h; omega

/-- The high word of a product below `2⁶⁴`. -/
theorem hi_word {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x).extractLsb' 32 32 = BitVec.ofNat 32 (x / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by omega))]

/-- Shoup's product of a word `y < 2q` by `w < q`, with `w' = ⌊w · 2³² / q⌋`, reduced. -/
theorem mulZ_word (y w w' : BitVec 32) (hy : y.toNat < 2 * 3329) (hw : w.toNat < 3329)
    (hw' : w'.toNat = w.toNat * 2 ^ 32 / 3329) :
    let t : BitVec 32 := (BitVec.ofNat 64 (y.toNat * w'.toNat)).extractLsb' 32 32
    let r := y * w - t * Q32
    (if r.toNat < (r - Q32).toNat then r else r - Q32) = BitVec.ofNat 32 (y.toNat * w.toNat % 3329) := by
  intro t r
  obtain ⟨b1, b2⟩ := shoup_bounds (a := y.toNat) (z := w.toNat) (q := 3329) (D := 2 ^ 32) (by decide)
    (by decide) (by omega)
  have hw'lt : w'.toNat < 2 ^ 32 := w'.isLt
  have hp : y.toNat * w'.toNat < 2 ^ 64 := by
    have := Nat.mul_lt_mul_of_lt_of_le (show y.toNat < 2 ^ 32 by omega) (Nat.le_of_lt hw'lt) (by decide)
    simpa using this
  have ht : t.toNat = y.toNat * (w.toNat * 2 ^ 32 / 3329) / 2 ^ 32 := by
    simp only [t, hi_word hp, BitVec.toNat_ofNat, hw']
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← hw']; omega))
  generalize hT : y.toNat * (w.toNat * 2 ^ 32 / 3329) / 2 ^ 32 = T at b1 b2 ht
  have hyw : (y * w).toNat = y.toNat * w.toNat := by
    rw [BitVec.toNat_mul]; apply Nat.mod_eq_of_lt
    have := Nat.mul_lt_mul_of_lt_of_le hy (Nat.le_of_lt hw) (by decide); omega
  have htq : (t * Q32).toNat = T * 3329 := by
    rw [BitVec.toNat_mul, ht, show Q32.toNat = 3329 from rfl]; apply Nat.mod_eq_of_lt
    have := Nat.mul_lt_mul_of_lt_of_le hy (Nat.le_of_lt hw) (by decide); omega
  have hr : r.toNat = y.toNat * w.toNat - T * 3329 := by
    simp only [r]; rw [BitVec.toNat_sub, hyw, htq]; omega
  rw [minq (by rw [hr]; omega), hr, Nat.mul_comm T, Nat.sub_mul_mod (by rw [Nat.mul_comm]; exact b1)]

/-! ## The instructions, word by word -/

theorem exec_vadd (d n m : VReg) (s : State) :
    exec (.vop (.add false d n m)) s = some (s.writeV d (ofVWords fun i => vword (s.vpr n) i + vword (s.vpr m) i)) :=
  rfl

theorem exec_vsub (d n m : VReg) (s : State) :
    exec (.vop (.sub true d n m)) s = some (s.writeV d (ofVWords fun i => vword (s.vpr n) i - vword (s.vpr m) i)) :=
  rfl

theorem exec_vminu (d n m : VReg) (s : State) :
    exec (.vop (.minu true d n m)) s = some (s.writeV d (ofVWords fun i =>
      if (vword (s.vpr n) i).toNat < (vword (s.vpr m) i).toNat then vword (s.vpr n) i else vword (s.vpr m) i)) :=
  rfl

theorem exec_vmuluwm (d n m : VReg) (s : State) :
    exec (.vop (.muluwm d n m)) s = some (s.writeV d (ofVWords fun i => vword (s.vpr n) i * vword (s.vpr m) i)) :=
  rfl

/-- The doubleword products of the even (`o = 0`) or odd (`o = 1`) words. -/
def mulD (o : Nat) (n m : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 64 ((vword n o).toNat * (vword m o).toNat) ++
    BitVec.ofNat 64 ((vword n (2 + o)).toNat * (vword m (2 + o)).toNat)

theorem exec_vmulE (d n m : VReg) (s : State) :
    exec (.vop (.mulu false true d n m)) s = some (s.writeV d (mulD 0 (s.vpr n) (s.vpr m))) := rfl

theorem exec_vmulO (d n m : VReg) (s : State) :
    exec (.vop (.mulu true true d n m)) s = some (s.writeV d (mulD 1 (s.vpr n) (s.vpr m))) := rfl

theorem exec_perm (d n m c : VReg) (s : State) :
    exec (.vop (.perm d n m c)) s = some (s.writeV d (permV (s.vpr n) (s.vpr m) (s.vpr c))) := rfl

theorem vword_qVec {i : Nat} (hi : i < 4) : vword qVec i = Q32 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> decide

/-- The high words of the products gathered in word order. -/
theorem vword_hi (n m : BitVec 128) {i : Nat} (hi : i < 4) :
    vword (permV (mulD 0 n m) (mulD 1 n m) ctlHi) i =
      (BitVec.ofNat 64 ((vword n i).toNat * (vword m i).toNat)).extractLsb' 32 32 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [vword_permV _ _ _ (k := 0) (by decide) (by decide) (by decide), mulD, vword_dwords _ _ (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 4) (by decide) (by decide) (by decide)]
    simp only [show ¬ (4 : Nat) < 4 by decide, ↓reduceIte, Nat.sub_self, mulD]
    rw [vword_dwords _ _ (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 2) (by decide) (by decide) (by decide), mulD, vword_dwords _ _ (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 6) (by decide) (by decide) (by decide)]
    simp only [show ¬ (6 : Nat) < 4 by decide, ↓reduceIte, Nat.reduceSub, mulD]
    rw [vword_dwords _ _ (by decide)]; rfl

/-! ## The butterflies -/

/-- What `vbfly` needs: words of `v6`, `v7` and the zeta `v4` below `q`, `ζ'`
in `v5`, `q` in `v0` and the gathering control in `v1`. -/
structure BIn (s : State) : Prop where
  x : ∀ i < 4, (vword (s.vpr .v6) i).toNat < 3329
  y : ∀ i < 4, (vword (s.vpr .v7) i).toNat < 3329
  w : ∀ i < 4, (vword (s.vpr .v4) i).toNat < 3329
  w' : ∀ i < 4, (vword (s.vpr .v5) i).toNat = (vword (s.vpr .v4) i).toNat * 2 ^ 32 / 3329
  q : s.vpr .v0 = qVec
  c : s.vpr .v1 = ctlHi

/-- The butterfly's results, word by word. -/
def bx (x y w : BitVec 32) : BitVec 32 := BitVec.ofNat 32 ((x.toNat + y.toNat * w.toNat % 3329) % 3329)
def by' (x y w : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 ((x.toNat + 3329 - y.toNat * w.toNat % 3329) % 3329)

theorem vbfly_ok {s : State} (h : BIn s) :
    WP isa (.block vbfly) s fun s' =>
      (∀ i < 4, vword (s'.vpr .v6) i = bx (vword (s.vpr .v6) i) (vword (s.vpr .v7) i) (vword (s.vpr .v4) i)) ∧
      (∀ i < 4, vword (s'.vpr .v7) i = by' (vword (s.vpr .v6) i) (vword (s.vpr .v7) i) (vword (s.vpr .v4) i)) ∧
      VOnly [.v6, .v7, .v8, .v9, .v10] s s' := by
  apply WP.of_runBlock
  simp only [vbfly, mulZ, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec_vmulE, exec_vmulO, exec_perm, exec_vmuluwm, exec_vsub, exec_vminu, exec_vadd, vpr_writeV,
    Option.some.injEq, exists_eq_left', reduceCtorEq, ite_true, ite_false, h.q, h.c]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV], by simp only [lr_writeV]⟩⟩
  rotate_right
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n6, n7, n8, n9, n10⟩ := hr
    simp only [vpr_writeV, n6, n7, n8, n9, n10, ite_false]
  all_goals
    have mz := mulZ_word (vword (s.vpr .v7) i) (vword (s.vpr .v4) i) (vword (s.vpr .v5) i)
      (by have := h.y i hi; omega) (h.w i hi) (h.w' i hi)
    simp only [vword_ofVWords _ hi, vword_hi _ _ hi, vword_qVec hi] at mz ⊢
    rw [mz]
    have hx := h.x i hi
    have hm : (BitVec.ofNat 32 ((vword (s.vpr .v7) i).toNat * (vword (s.vpr .v4) i).toNat % 3329)).toNat =
        (vword (s.vpr .v7) i).toNat * (vword (s.vpr .v4) i).toNat % 3329 := by
      rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; have := Nat.mod_lt ((vword (s.vpr .v7) i).toNat *
        (vword (s.vpr .v4) i).toNat) (show 3329 > 0 by decide); omega
    have hlt := Nat.mod_lt ((vword (s.vpr .v7) i).toNat * (vword (s.vpr .v4) i).toNat) (show 3329 > 0 by decide)
  · rw [minq (by rw [BitVec.toNat_add, hm]; omega), bx, BitVec.toNat_add, hm]
    congr 1; omega
  · rw [minq (by rw [BitVec.toNat_sub, BitVec.toNat_add, hm, show Q32.toNat = 3329 from rfl]; omega), by',
      BitVec.toNat_sub, BitVec.toNat_add, hm, show Q32.toNat = 3329 from rfl]
    exact congrArg (BitVec.ofNat 32) (by omega)

/-- The inverse butterfly's results, word by word. -/
def ix (x y : BitVec 32) : BitVec 32 := BitVec.ofNat 32 ((x.toNat + y.toNat) % 3329)
def iy (x y w : BitVec 32) : BitVec 32 := BitVec.ofNat 32 ((y.toNat + 3329 - x.toNat) * w.toNat % 3329)

theorem vibfly_ok {s : State} (h : BIn s) :
    WP isa (.block vibfly) s fun s' =>
      (∀ i < 4, vword (s'.vpr .v6) i = ix (vword (s.vpr .v6) i) (vword (s.vpr .v7) i)) ∧
      (∀ i < 4, vword (s'.vpr .v8) i = iy (vword (s.vpr .v6) i) (vword (s.vpr .v7) i) (vword (s.vpr .v4) i)) ∧
      VOnly [.v6, .v7, .v8, .v9, .v10] s s' := by
  apply WP.of_runBlock
  simp only [vibfly, mulZ, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec_vmulE, exec_vmulO, exec_perm, exec_vmuluwm, exec_vsub, exec_vminu, exec_vadd, vpr_writeV,
    Option.some.injEq, exists_eq_left', reduceCtorEq, ite_true, ite_false, h.q, h.c]
  refine ⟨fun i hi => ?_, fun i hi => ?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV], by simp only [lr_writeV]⟩⟩
  · have hx := h.x i hi
    have hy := h.y i hi
    simp only [vword_ofVWords _ hi, vword_qVec hi]
    rw [minq (by rw [BitVec.toNat_add]; omega), ix, BitVec.toNat_add]
    exact congrArg (BitVec.ofNat 32) (by omega)
  · have hx := h.x i hi
    have hy := h.y i hi
    have hY : (vword (s.vpr .v7) i + Q32 - vword (s.vpr .v6) i).toNat =
        (vword (s.vpr .v7) i).toNat + 3329 - (vword (s.vpr .v6) i).toNat := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, show Q32.toNat = 3329 from rfl]; omega
    have mz := mulZ_word (vword (s.vpr .v7) i + Q32 - vword (s.vpr .v6) i) (vword (s.vpr .v4) i)
      (vword (s.vpr .v5) i) (by rw [hY]; omega) (h.w i hi) (h.w' i hi)
    simp only [vword_ofVWords _ hi, vword_hi _ _ hi, vword_qVec hi] at mz ⊢
    rw [mz, iy, hY]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n6, n7, n8, n9, n10⟩ := hr
    simp only [vpr_writeV, n6, n7, n8, n9, n10, ite_false]

/-! ## Rows of four coefficients -/

section
open VG.Proof.MlKem VG.Spec.MlKem

theorem coeffAddr_add (F : Addr) (j q : Nat) :
    coeffAddr F j + BitVec.ofNat 64 (4 * q) = coeffAddr F (j + q) := by
  rw [coeffAddr, coeffAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

/-- The words of a row of coefficients loaded by `lxvd2x`: `1, 0, 3, 2`. -/
theorem row_lane {m : Mem} {F : Addr} {f : Poly} (h : PolyIs m F f) {j : Nat} (hj : j + 4 ≤ 256) {p : Nat}
    (hp : p < 4) : vword (swapDwords (m.read (coeffAddr F j) 16)) p = BitVec.ofNat 32 (f[j + (p ^^^ 1)]!).val := by
  rw [vword_load _ _ hp, coeffAddr_add, ← coeffAt_eq]
  exact polyIs_coeffAt h (by have := xor1_lt hp; rw [n_eq]; omega)

/-- A coefficient after `stxvd2x` of a row from `j`. -/
theorem coeffAt_row (m : Mem) (F : Addr) (j : Nat) (v : BitVec 128) {i : Nat} (hi : i < 256)
    (hj : j + 4 ≤ 256) :
    coeffAt (m.write (coeffAddr F j) 16 (swapDwords v)) F i =
      if j ≤ i ∧ i < j + 4 then vword v ((i - j) ^^^ 1) else coeffAt m F i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr F i = coeffAddr F j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [coeffAddr_add, show j + (i - j) = i by omega]]
    exact readW_store _ _ _ (by omega)
  · have hw : m.write (coeffAddr F j) 16 (swapDwords v) = m.writeW (coeffAddr F j) (swapDwords v) := by
      simp only [Mem.writeW, BitVec.setWidth_eq]
    rw [hw]
    exact Mem.readW_writeW_sep (Offset.sep F (by omega) (by omega) (by omega)) (by decide)

/-- Two rows stored over a polynomial. -/
theorem polyIs_rows {m : Mem} {F : Addr} {f g : Poly} (h : PolyIs m F f) {j₁ j₂ : Nat}
    (h1 : j₁ + 4 ≤ 256) (h2 : j₂ + 4 ≤ 256) {A B : BitVec 128}
    (hA : ∀ p < 4, vword A p = BitVec.ofNat 32 (g[j₁ + (p ^^^ 1)]!).val)
    (hB : ∀ p < 4, vword B p = BitVec.ofNat 32 (g[j₂ + (p ^^^ 1)]!).val)
    (hf : ∀ i < 256, ¬ (j₁ ≤ i ∧ i < j₁ + 4) → ¬ (j₂ ≤ i ∧ i < j₂ + 4) → g[i]! = f[i]!) :
    PolyIs ((m.write (coeffAddr F j₁) 16 (swapDwords A)).write (coeffAddr F j₂) 16 (swapDwords B)) F g := by
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [n_eq] at hi
  rw [coeffAt_row _ _ _ _ hi h2, coeffAt_row _ _ _ _ hi h1]
  by_cases r2 : j₂ ≤ i ∧ i < j₂ + 4
  · have l := xor1_lt (e := i - j₂) (by omega); have e := xor1_xor1 (i - j₂)
    rw [ite_eq_left r2, hB _ l, e, Nat.add_sub_cancel' r2.1]
  rw [ite_eq_right r2]
  by_cases r1 : j₁ ≤ i ∧ i < j₁ + 4
  · have l := xor1_lt (e := i - j₁) (by omega); have e := xor1_xor1 (i - j₁)
    rw [ite_eq_left r1, hA _ l, e, Nat.add_sub_cancel' r1.1]
  rw [ite_eq_right r1, polyIs_coeffAt h (by rw [n_eq]; exact hi), hf i hi r1 r2]

theorem toNat_val32 (a : Zq) : (BitVec.ofNat 32 a.val).toNat = a.val := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := val_lt a; omega)

theorem bx_val (a b z : Zq) :
    bx (BitVec.ofNat 32 a.val) (BitVec.ofNat 32 b.val) (BitVec.ofNat 32 z.val) = BitVec.ofNat 32 (a + z * b).val := by
  rw [bx, toNat_val32, toNat_val32, toNat_val32, val_add', val_mul, Nat.mul_comm z.val]

theorem by'_val (a b z : Zq) :
    by' (BitVec.ofNat 32 a.val) (BitVec.ofNat 32 b.val) (BitVec.ofNat 32 z.val) = BitVec.ofNat 32 (a - z * b).val := by
  rw [by', toNat_val32, toNat_val32, toNat_val32, val_sub', val_mul, Nat.mul_comm z.val]
  have := Nat.mod_lt (b.val * z.val) (show 0 < 3329 by decide)
  congr 2; show _ = a.val + (3329 - b.val * z.val % 3329); omega

end

/-! ## The body of the inner loop -/

/-- What a step of the inner loop keeps. -/
structure Kept (s s' : State) : Prop where
  g : ∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r10 → s'.gpr r = s.gpr r
  v : ∀ v, v ≠ .v6 → v ≠ .v7 → v ≠ .v8 → v ≠ .v9 → v ≠ .v10 → s'.vpr v = s.vpr v
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr

theorem body_ok {s : State} (ia : InRegions (s.rd ++ s.wr) (s.gpr .r3 + s.gpr .r5) 16)
    (ib : InRegions (s.rd ++ s.wr) (s.gpr .r3 + s.gpr .r6) 16)
    (oa : InRegions s.wr (s.gpr .r3 + s.gpr .r5) 16) (ob : InRegions s.wr (s.gpr .r3 + s.gpr .r6) 16)
    (hx : ∀ i < 4, (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r5) 16)) i).toNat < 3329)
    (hy : ∀ i < 4, (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r6) 16)) i).toNat < 3329)
    (hw : ∀ i < 4, (vword (s.vpr .v4) i).toNat < 3329)
    (hw' : ∀ i < 4, (vword (s.vpr .v5) i).toNat = (vword (s.vpr .v4) i).toNat * 2 ^ 32 / 3329)
    (hq : s.vpr .v0 = qVec) (hc : s.vpr .v1 = ctlHi) :
    WP isa (.block vbflyBody) s fun s' => ∃ A B : BitVec 128,
      (∀ i < 4, vword A i = bx (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r5) 16)) i)
        (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r6) 16)) i) (vword (s.vpr .v4) i)) ∧
      (∀ i < 4, vword B i = by' (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r5) 16)) i)
        (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r6) 16)) i) (vword (s.vpr .v4) i)) ∧
      s'.mem = (s.mem.write (s.gpr .r3 + s.gpr .r5) 16 (swapDwords A)).write (s.gpr .r3 + s.gpr .r6) 16
        (swapDwords B) ∧
      s'.gpr .r5 = s.gpr .r5 + 16 ∧ s'.gpr .r6 = s.gpr .r6 + 16 ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
      Kept s s' := by
  rw [vbflyBody, WP.block_append_iff, WP.block_append_iff]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_lxvd2x .v6 .r3 .r5 s (by decide) ia, runStep_some, runBlock_cons,
    exec_lxvd2x .v7 .r3 .r6 _ (by decide) (by exact ib), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_⟩
  refine WP.mono (vbfly_ok ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩)
    fun s₂ ⟨h6, h7, hv⟩ => ?_
  · simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]; exact hx i hi
  · simp only [vpr_writeV, ite_true]; exact hy i hi
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hw i hi
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hw' i hi
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hq
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hc
  have g₂ : s₂.gpr = s.gpr := hv.gpr
  have oa' : InRegions s₂.wr (s₂.gpr .r3 + s₂.gpr .r5) 16 := by rw [hv.wr, g₂]; exact oa
  have ob' : InRegions s₂.wr (s₂.gpr .r3 + s₂.gpr .r6) 16 := by rw [hv.wr, g₂]; exact ob
  apply WP.of_runBlock
  rw [runBlock_cons, exec_stxvd2x .v6 .r3 .r5 s₂ (by decide) oa', runStep_some, runBlock_cons,
    exec_stxvd2x .v7 .r3 .r6 _ (by decide) (by exact ob'), runStep_some, runBlock_cons,
    exec_addi (by decide) (by decide), runStep_some, runBlock_cons, exec_addi (by decide) (by decide), runStep_some,
    runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  refine ⟨_, rfl, s₂.vpr .v6, s₂.vpr .v7, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ⟨fun r h5 h6' h10 => ?_,
    fun v n6 n7 n8 n9 n10 => ?_, hv.rd, hv.wr, hv.sp, hv.lr⟩⟩
  · rw [h6 i hi]; simp only [vpr_writeV, mem_writeV, gpr_writeV, reduceCtorEq, ite_true, ite_false]
  · rw [h7 i hi]; simp only [vpr_writeV, mem_writeV, gpr_writeV, reduceCtorEq, ite_true, ite_false]
  · simp only [State.write, hv.mem, g₂, mem_writeV]
  · simp only [RegUpd.gpr_write, g₂, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_write, g₂, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_write, g₂, ite_true]; rfl
  · simp only [RegUpd.gpr_write, g₂, h5, h6', h10, ite_false]
  · show s₂.vpr v = s.vpr v
    rw [hv.v v (by simp [n6, n7, n8, n9, n10])]
    simp only [vpr_writeV, n6, n7, ite_false]

/-! ## The last layer: two blocks of `len = 2` per step -/

theorem vword_lo (n m : BitVec 128) {p : Nat} (hp : p < 4) :
    vword (permV n m ctlLo) p = if p < 2 then vword n p else vword m (p - 2) := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl
  · rw [vword_permV _ _ _ (k := 0) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 1) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 4) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 5) (by decide) (by decide) (by decide)]; rfl

theorem vword_hi2 (n m : BitVec 128) {p : Nat} (hp : p < 4) :
    vword (permV n m ctlHi2) p = if p < 2 then vword n (p + 2) else vword m p := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl
  · rw [vword_permV _ _ _ (k := 2) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 3) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 6) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 7) (by decide) (by decide) (by decide)]; rfl

theorem vword_pw (n : BitVec 128) {p : Nat} (hp : p < 4) :
    vword (permV n n ctlPw) p = vword n (if p < 2 then 1 else 3) := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl
  · rw [vword_permV _ _ _ (k := 1) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 1) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 3) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 3) (by decide) (by decide) (by decide)]; rfl

theorem vword_pwp (n : BitVec 128) {p : Nat} (hp : p < 4) :
    vword (permV n n ctlPwp) p = vword n (if p < 2 then 0 else 2) := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl
  · rw [vword_permV _ _ _ (k := 0) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 0) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 2) (by decide) (by decide) (by decide)]; rfl
  · rw [vword_permV _ _ _ (k := 2) (by decide) (by decide) (by decide)]; rfl

/-- What a step of the last layer keeps. -/
structure Kept2 (s s' : State) : Prop where
  g : ∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r10 → s'.gpr r = s.gpr r
  v : ∀ v, v ≠ .v4 → v ≠ .v5 → v ≠ .v6 → v ≠ .v7 → v ≠ .v8 → v ≠ .v9 → v ≠ .v10 → v ≠ .v11 →
    s'.vpr v = s.vpr v
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr

/-- A step of the last layer: the rows `R` and `T` of four coefficients and
the zetas `Z` (`ζ'ₖ, ζₖ, ζ'ₖ₊₁, ζₖ₊₁`). -/
theorem body2_ok {s : State} {R T Z : BitVec 128}
    (iz : InRegions (s.rd ++ s.wr) (s.gpr .r4 + s.gpr .r7) 16)
    (ia : InRegions (s.rd ++ s.wr) (s.gpr .r3 + s.gpr .r5) 16)
    (ib : InRegions (s.rd ++ s.wr) (s.gpr .r3 + (s.gpr .r5 + BitVec.ofNat 64 16)) 16)
    (oa : InRegions s.wr (s.gpr .r3 + s.gpr .r5) 16)
    (ob : InRegions s.wr (s.gpr .r3 + (s.gpr .r5 + BitVec.ofNat 64 16)) 16)
    (eZ : swapDwords (s.mem.read (s.gpr .r4 + s.gpr .r7) 16) = Z)
    (eR : swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r5) 16) = R)
    (eT : swapDwords (s.mem.read (s.gpr .r3 + (s.gpr .r5 + BitVec.ofNat 64 16)) 16) = T)
    (hR : ∀ i < 4, (vword R i).toNat < 3329) (hT : ∀ i < 4, (vword T i).toNat < 3329)
    (hz1 : (vword Z 1).toNat < 3329) (hz3 : (vword Z 3).toNat < 3329)
    (hz0 : (vword Z 0).toNat = (vword Z 1).toNat * 2 ^ 32 / 3329)
    (hz2 : (vword Z 2).toNat = (vword Z 3).toNat * 2 ^ 32 / 3329)
    (h0 : s.vpr .v0 = qVec) (h1 : s.vpr .v1 = ctlHi) (h2 : s.vpr .v2 = ctlLo) (h3 : s.vpr .v3 = ctlHi2)
    (h12 : s.vpr .v12 = ctlPw) (h13 : s.vpr .v13 = ctlPwp) :
    WP isa (.block vbfly2Body) s fun s' => ∃ A B : BitVec 128,
      (∀ p < 4, vword A p = if p < 2 then bx (vword R p) (vword R (p + 2)) (vword Z 1)
        else by' (vword R (p - 2)) (vword R p) (vword Z 1)) ∧
      (∀ p < 4, vword B p = if p < 2 then bx (vword T p) (vword T (p + 2)) (vword Z 3)
        else by' (vword T (p - 2)) (vword T p) (vword Z 3)) ∧
      s'.mem = (s.mem.write (s.gpr .r3 + s.gpr .r5) 16 (swapDwords A)).write
        (s.gpr .r3 + (s.gpr .r5 + BitVec.ofNat 64 16)) 16 (swapDwords B) ∧
      s'.gpr .r5 = s.gpr .r5 + BitVec.ofNat 64 32 ∧ s'.gpr .r7 = s.gpr .r7 + BitVec.ofNat 64 16 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧ Kept2 s s' := by
  rw [vbfly2Body, WP.block_append_iff, WP.block_append_iff]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec_perm, exec_lxvd2x .v11 .r4 .r7 s (by decide) iz,
    exec_addi (show Reg.r5 ≠ .r0 by decide) (show 16 < 2 ^ 15 by decide)]
  rw [exec_lxvd2x .v8 .r3 .r5 _ (by decide) (by exact ia), runStep_some, runBlock_cons,
    exec_lxvd2x .v9 .r3 .r6 _ (by decide) (by exact ib), runStep_some, runBlock_cons, exec_perm, runStep_some,
    runBlock_cons, exec_perm, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_⟩
  simp only [vpr_writeV, vpr_write, reduceCtorEq, ite_true, ite_false, eZ, h2, h3, h12, h13]
  refine WP.mono (vbfly_ok ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩)
    fun s₂ ⟨h6, h7, hv⟩ => ?_
  · simp only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write, RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false]
    rw [vword_lo _ _ hi]; split
    · exact hR _ hi
    · exact hT _ (by omega)
  · simp only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write, RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false]
    rw [vword_hi2 _ _ hi]; split
    · exact hR _ (by omega)
    · exact hT _ hi
  · simp only [vpr_writeV, vpr_write, reduceCtorEq, ite_false, ite_true]
    rw [vword_pw _ hi]; split
    · exact hz1
    · exact hz3
  · simp only [vpr_writeV, vpr_write, reduceCtorEq, ite_false, ite_true]
    rw [vword_pw _ hi, vword_pwp _ hi]; split
    · exact hz0
    · exact hz2
  · simp only [vpr_writeV, vpr_write, reduceCtorEq, ite_false]; exact h0
  · simp only [vpr_writeV, vpr_write, reduceCtorEq, ite_false]; exact h1
  have g₂ : ∀ r, s₂.gpr r = if r = .r6 then s.gpr .r5 + BitVec.ofNat 64 16 else s.gpr r := fun r => by
    rw [hv.gpr]; rfl
  have m₂ : s₂.mem = s.mem := hv.mem
  have v₂ : ∀ v, v ≠ .v4 → v ≠ .v5 → v ≠ .v6 → v ≠ .v7 → v ≠ .v8 → v ≠ .v9 → v ≠ .v10 → v ≠ .v11 →
      s₂.vpr v = s.vpr v := fun v n4 n5 n6 n7 n8 n9 n10 n11 => by
    rw [hv.v v (by simp [n6, n7, n8, n9, n10])]
    simp only [vpr_writeV, vpr_write, n4, n5, n6, n7, n8, n9, n11, ite_false]
  have oa' : InRegions s₂.wr (s₂.gpr .r3 + s₂.gpr .r5) 16 := by
    rw [hv.wr, g₂, g₂]; simpa only [wr_writeV, RegUpd.wr_write, reduceCtorEq, ite_false] using oa
  have ob' : InRegions s₂.wr (s₂.gpr .r3 + s₂.gpr .r6) 16 := by
    rw [hv.wr, g₂, g₂]; simpa only [wr_writeV, RegUpd.wr_write, reduceCtorEq, ite_false, ite_true] using ob
  apply WP.of_runBlock
  rw [runBlock_cons, exec_perm, runStep_some, runBlock_cons, exec_perm, runStep_some, runBlock_cons,
    exec_stxvd2x .v8 .r3 .r5 _ (by decide) (by exact oa'), runStep_some, runBlock_cons,
    exec_stxvd2x .v9 .r3 .r6 _ (by decide) (by exact ob'), runStep_some, runBlock_cons,
    exec_addi (by decide) (by decide), runStep_some, runBlock_cons, exec_addi (by decide) (by decide), runStep_some,
    runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  have e2 := v₂ .v2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e3 := v₂ .v3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨_, rfl, permV (s₂.vpr .v6) (s₂.vpr .v7) ctlLo, permV (s₂.vpr .v6) (s₂.vpr .v7) ctlHi2,
    fun p hp => ?_, fun p hp => ?_, ?_, ?_, ?_, ?_, ⟨fun r h5 h6' h7' h10 => ?_,
    fun v n4 n5 n6 n7 n8 n9 n10 n11 => ?_, hv.rd, hv.wr, hv.sp, hv.lr⟩⟩
  · rw [vword_lo _ _ hp]
    split
    · rw [h6 p hp]
      simp (disch := omega) only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write,
        RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false, vword_lo, vword_hi2, vword_pw,
        ↓ite_eq_left]
    · rw [h7 (p - 2) (by omega)]
      simp (disch := omega) only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write,
        RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false, vword_lo, vword_hi2, vword_pw,
        ↓ite_eq_left, Nat.sub_add_cancel]
  · rw [vword_hi2 _ _ hp]
    split
    · rw [h6 (p + 2) (by omega)]
      simp (disch := omega) only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write,
        RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false, vword_lo, vword_hi2, vword_pw,
        ↓ite_eq_right, Nat.add_sub_cancel]
    · rw [h7 p hp]
      simp (disch := omega) only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write,
        RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false, vword_lo, vword_hi2, vword_pw,
        ↓ite_eq_right]
  · show (s₂.mem.write _ 16 _).write _ 16 _ = _
    simp only [m₂, gpr_writeV, vpr_writeV, g₂, e2, e3, h2, h3, reduceCtorEq, ite_false, ite_true]
  · simp only [RegUpd.gpr_write, gpr_writeV, g₂, ite_true, ite_false, reduceCtorEq]
  · simp only [RegUpd.gpr_write, gpr_writeV, g₂, ite_true, ite_false, reduceCtorEq]
  · simp only [RegUpd.gpr_write, gpr_writeV, g₂, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_write, gpr_writeV, g₂, h5, h6', h7', h10, ite_false]
  · simp only [vpr_writeV, vpr_write, n8, n9, ite_false]
    exact v₂ v n4 n5 n6 n7 n8 n9 n10 n11

/-! ## The inverse NTT's bodies -/

theorem ibody_ok {s : State} (ia : InRegions (s.rd ++ s.wr) (s.gpr .r3 + s.gpr .r5) 16)
    (ib : InRegions (s.rd ++ s.wr) (s.gpr .r3 + s.gpr .r6) 16)
    (oa : InRegions s.wr (s.gpr .r3 + s.gpr .r5) 16) (ob : InRegions s.wr (s.gpr .r3 + s.gpr .r6) 16)
    (hx : ∀ i < 4, (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r5) 16)) i).toNat < 3329)
    (hy : ∀ i < 4, (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r6) 16)) i).toNat < 3329)
    (hw : ∀ i < 4, (vword (s.vpr .v4) i).toNat < 3329)
    (hw' : ∀ i < 4, (vword (s.vpr .v5) i).toNat = (vword (s.vpr .v4) i).toNat * 2 ^ 32 / 3329)
    (hq : s.vpr .v0 = qVec) (hc : s.vpr .v1 = ctlHi) :
    WP isa (.block vibflyBody) s fun s' => ∃ A B : BitVec 128,
      (∀ i < 4, vword A i = ix (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r5) 16)) i)
        (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r6) 16)) i)) ∧
      (∀ i < 4, vword B i = iy (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r5) 16)) i)
        (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r6) 16)) i) (vword (s.vpr .v4) i)) ∧
      s'.mem = (s.mem.write (s.gpr .r3 + s.gpr .r5) 16 (swapDwords A)).write (s.gpr .r3 + s.gpr .r6) 16
        (swapDwords B) ∧
      s'.gpr .r5 = s.gpr .r5 + 16 ∧ s'.gpr .r6 = s.gpr .r6 + 16 ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
      Kept s s' := by
  rw [vibflyBody, WP.block_append_iff, WP.block_append_iff]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_lxvd2x .v6 .r3 .r5 s (by decide) ia, runStep_some, runBlock_cons,
    exec_lxvd2x .v7 .r3 .r6 _ (by decide) (by exact ib), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_⟩
  refine WP.mono (vibfly_ok ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩)
    fun s₂ ⟨h6, h7, hv⟩ => ?_
  · simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]; exact hx i hi
  · simp only [vpr_writeV, ite_true]; exact hy i hi
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hw i hi
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hw' i hi
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hq
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hc
  have g₂ : s₂.gpr = s.gpr := hv.gpr
  have oa' : InRegions s₂.wr (s₂.gpr .r3 + s₂.gpr .r5) 16 := by rw [hv.wr, g₂]; exact oa
  have ob' : InRegions s₂.wr (s₂.gpr .r3 + s₂.gpr .r6) 16 := by rw [hv.wr, g₂]; exact ob
  apply WP.of_runBlock
  rw [runBlock_cons, exec_stxvd2x .v6 .r3 .r5 s₂ (by decide) oa', runStep_some, runBlock_cons,
    exec_stxvd2x .v8 .r3 .r6 _ (by decide) (by exact ob'), runStep_some, runBlock_cons,
    exec_addi (by decide) (by decide), runStep_some, runBlock_cons, exec_addi (by decide) (by decide), runStep_some,
    runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  refine ⟨_, rfl, s₂.vpr .v6, s₂.vpr .v8, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ⟨fun r h5 h6' h10 => ?_,
    fun v n6 n7 n8 n9 n10 => ?_, hv.rd, hv.wr, hv.sp, hv.lr⟩⟩
  · rw [h6 i hi]; simp only [vpr_writeV, mem_writeV, gpr_writeV, reduceCtorEq, ite_true, ite_false]
  · rw [h7 i hi]; simp only [vpr_writeV, mem_writeV, gpr_writeV, reduceCtorEq, ite_true, ite_false]
  · simp only [State.write, hv.mem, g₂, mem_writeV]
  · simp only [RegUpd.gpr_write, g₂, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_write, g₂, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_write, g₂, ite_true]; rfl
  · simp only [RegUpd.gpr_write, g₂, h5, h6', h10, ite_false]
  · show s₂.vpr v = s.vpr v
    rw [hv.v v (by simp [n6, n7, n8, n9, n10])]
    simp only [vpr_writeV, n6, n7, ite_false]

/-- A step of the inverse NTT's first layer: the rows `R` and `T` of four
coefficients and the zetas `Z` (`ζ'ₖ, ζₖ, ζ'ₖ₊₁, ζₖ₊₁`), `ζₖ` that of `T`'s
block and `ζₖ₊₁` that of `R`'s. -/
theorem ibody2_ok {s : State} {R T Z : BitVec 128}
    (iz : InRegions (s.rd ++ s.wr) (s.gpr .r4 + s.gpr .r7) 16)
    (ia : InRegions (s.rd ++ s.wr) (s.gpr .r3 + s.gpr .r5) 16)
    (ib : InRegions (s.rd ++ s.wr) (s.gpr .r3 + (s.gpr .r5 + BitVec.ofNat 64 16)) 16)
    (oa : InRegions s.wr (s.gpr .r3 + s.gpr .r5) 16)
    (ob : InRegions s.wr (s.gpr .r3 + (s.gpr .r5 + BitVec.ofNat 64 16)) 16)
    (eZ : swapDwords (s.mem.read (s.gpr .r4 + s.gpr .r7) 16) = Z)
    (eR : swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r5) 16) = R)
    (eT : swapDwords (s.mem.read (s.gpr .r3 + (s.gpr .r5 + BitVec.ofNat 64 16)) 16) = T)
    (hR : ∀ i < 4, (vword R i).toNat < 3329) (hT : ∀ i < 4, (vword T i).toNat < 3329)
    (hz1 : (vword Z 1).toNat < 3329) (hz3 : (vword Z 3).toNat < 3329)
    (hz0 : (vword Z 0).toNat = (vword Z 1).toNat * 2 ^ 32 / 3329)
    (hz2 : (vword Z 2).toNat = (vword Z 3).toNat * 2 ^ 32 / 3329)
    (h0 : s.vpr .v0 = qVec) (h1 : s.vpr .v1 = ctlHi) (h2 : s.vpr .v2 = ctlLo) (h3 : s.vpr .v3 = ctlHi2)
    (h12 : s.vpr .v12 = ctlPw) (h13 : s.vpr .v13 = ctlPwp) :
    WP isa (.block vibfly2Body) s fun s' => ∃ A B : BitVec 128,
      (∀ p < 4, vword A p = if p < 2 then ix (vword T p) (vword T (p + 2))
        else iy (vword T (p - 2)) (vword T p) (vword Z 1)) ∧
      (∀ p < 4, vword B p = if p < 2 then ix (vword R p) (vword R (p + 2))
        else iy (vword R (p - 2)) (vword R p) (vword Z 3)) ∧
      s'.mem = (s.mem.write (s.gpr .r3 + (s.gpr .r5 + BitVec.ofNat 64 16)) 16 (swapDwords A)).write
        (s.gpr .r3 + s.gpr .r5) 16 (swapDwords B) ∧
      s'.gpr .r5 = s.gpr .r5 + BitVec.ofNat 64 32 ∧ s'.gpr .r7 = s.gpr .r7 - BitVec.ofNat 64 16 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧ Kept2 s s' := by
  rw [vibfly2Body, WP.block_append_iff, WP.block_append_iff]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec_perm, exec_lxvd2x .v11 .r4 .r7 s (by decide) iz,
    exec_addi (show Reg.r5 ≠ .r0 by decide) (show 16 < 2 ^ 15 by decide)]
  rw [exec_lxvd2x .v8 .r3 .r5 _ (by decide) (by exact ia), runStep_some, runBlock_cons,
    exec_lxvd2x .v9 .r3 .r6 _ (by decide) (by exact ib), runStep_some, runBlock_cons, exec_perm, runStep_some,
    runBlock_cons, exec_perm, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_⟩
  simp only [vpr_writeV, vpr_write, reduceCtorEq, ite_true, ite_false, eZ, h2, h3, h12, h13]
  refine WP.mono (vibfly_ok ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩)
    fun s₂ ⟨h6, h7, hv⟩ => ?_
  · simp only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write, RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false]
    rw [vword_lo _ _ hi]; split
    · exact hT _ hi
    · exact hR _ (by omega)
  · simp only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write, RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false]
    rw [vword_hi2 _ _ hi]; split
    · exact hT _ (by omega)
    · exact hR _ hi
  · simp only [vpr_writeV, vpr_write, reduceCtorEq, ite_false, ite_true]
    rw [vword_pw _ hi]; split
    · exact hz1
    · exact hz3
  · simp only [vpr_writeV, vpr_write, reduceCtorEq, ite_false, ite_true]
    rw [vword_pw _ hi, vword_pwp _ hi]; split
    · exact hz0
    · exact hz2
  · simp only [vpr_writeV, vpr_write, reduceCtorEq, ite_false]; exact h0
  · simp only [vpr_writeV, vpr_write, reduceCtorEq, ite_false]; exact h1
  have g₂ : ∀ r, s₂.gpr r = if r = .r6 then s.gpr .r5 + BitVec.ofNat 64 16 else s.gpr r := fun r => by
    rw [hv.gpr]; rfl
  have m₂ : s₂.mem = s.mem := hv.mem
  have v₂ : ∀ v, v ≠ .v4 → v ≠ .v5 → v ≠ .v6 → v ≠ .v7 → v ≠ .v8 → v ≠ .v9 → v ≠ .v10 → v ≠ .v11 →
      s₂.vpr v = s.vpr v := fun v n4 n5 n6 n7 n8 n9 n10 n11 => by
    rw [hv.v v (by simp [n6, n7, n8, n9, n10])]
    simp only [vpr_writeV, vpr_write, n4, n5, n6, n7, n8, n9, n11, ite_false]
  have oa' : InRegions s₂.wr (s₂.gpr .r3 + s₂.gpr .r5) 16 := by
    rw [hv.wr, g₂, g₂]; simpa only [wr_writeV, RegUpd.wr_write, reduceCtorEq, ite_false] using oa
  have ob' : InRegions s₂.wr (s₂.gpr .r3 + s₂.gpr .r6) 16 := by
    rw [hv.wr, g₂, g₂]; simpa only [wr_writeV, RegUpd.wr_write, reduceCtorEq, ite_false, ite_true] using ob
  apply WP.of_runBlock
  rw [runBlock_cons, exec_perm, runStep_some, runBlock_cons, exec_perm, runStep_some, runBlock_cons,
    exec_stxvd2x .v9 .r3 .r6 _ (by decide) (by exact ob'), runStep_some, runBlock_cons,
    exec_stxvd2x .v10 .r3 .r5 _ (by decide) (by exact oa'), runStep_some, runBlock_cons,
    exec_addi (by decide) (by decide), runStep_some, runBlock_cons, exec_subi (by decide) (by decide), runStep_some,
    runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  have e2 := v₂ .v2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e3 := v₂ .v3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨_, rfl, permV (s₂.vpr .v6) (s₂.vpr .v8) ctlLo, permV (s₂.vpr .v6) (s₂.vpr .v8) ctlHi2,
    fun p hp => ?_, fun p hp => ?_, ?_, ?_, ?_, ?_, ⟨fun r h5 h6' h7' h10 => ?_,
    fun v n4 n5 n6 n7 n8 n9 n10 n11 => ?_, hv.rd, hv.wr, hv.sp, hv.lr⟩⟩
  · rw [vword_lo _ _ hp]
    split
    · rw [h6 p hp]
      simp (disch := omega) only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write,
        RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false, vword_lo, vword_hi2,
        ↓ite_eq_left]
    · rw [h7 (p - 2) (by omega)]
      simp (disch := omega) only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write,
        RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false, vword_lo, vword_hi2, vword_pw,
        ↓ite_eq_left, Nat.sub_add_cancel]
  · rw [vword_hi2 _ _ hp]
    split
    · rw [h6 (p + 2) (by omega)]
      simp (disch := omega) only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write,
        RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false, vword_lo, vword_hi2,
        ↓ite_eq_right, Nat.add_sub_cancel]
    · rw [h7 p hp]
      simp (disch := omega) only [vpr_writeV, vpr_write, mem_writeV, gpr_writeV, RegUpd.mem_write,
        RegUpd.gpr_write, eR, eT, reduceCtorEq, ite_true, ite_false, vword_lo, vword_hi2, vword_pw,
        ↓ite_eq_right]
  · show (s₂.mem.write _ 16 _).write _ 16 _ = _
    simp only [m₂, gpr_writeV, vpr_writeV, g₂, e2, e3, h2, h3, reduceCtorEq, ite_false, ite_true]
  · simp only [RegUpd.gpr_write, gpr_writeV, g₂, ite_true, ite_false, reduceCtorEq]
  · simp only [RegUpd.gpr_write, gpr_writeV, g₂, ite_true, ite_false, reduceCtorEq]
  · simp only [RegUpd.gpr_write, gpr_writeV, g₂, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_write, gpr_writeV, g₂, h5, h6', h7', h10, ite_false]
  · simp only [vpr_writeV, vpr_write, n9, n10, ite_false]
    exact v₂ v n4 n5 n6 n7 n8 n9 n10 n11

/-- `mulZ` alone, on words of `v7` below `2q`. -/
theorem mulZ_ok {s : State} (hy : ∀ i < 4, (vword (s.vpr .v7) i).toNat < 2 * 3329)
    (hw : ∀ i < 4, (vword (s.vpr .v4) i).toNat < 3329)
    (hw' : ∀ i < 4, (vword (s.vpr .v5) i).toNat = (vword (s.vpr .v4) i).toNat * 2 ^ 32 / 3329)
    (hq : s.vpr .v0 = qVec) (hc : s.vpr .v1 = ctlHi) :
    WP isa (.block mulZ) s fun s' =>
      (∀ i < 4, vword (s'.vpr .v8) i =
        BitVec.ofNat 32 ((vword (s.vpr .v7) i).toNat * (vword (s.vpr .v4) i).toNat % 3329)) ∧
      VOnly [.v8, .v9] s s' := by
  apply WP.of_runBlock
  simp only [mulZ, runBlock_cons, runStep_some, runBlock_nil,
    exec_vmulE, exec_vmulO, exec_perm, exec_vmuluwm, exec_vsub, exec_vminu, vpr_writeV,
    Option.some.injEq, exists_eq_left', reduceCtorEq, ite_true, ite_false, hq, hc]
  refine ⟨fun i hi => ?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV], by simp only [lr_writeV]⟩⟩
  · have mz := mulZ_word (vword (s.vpr .v7) i) (vword (s.vpr .v4) i) (vword (s.vpr .v5) i) (hy i hi) (hw i hi)
      (hw' i hi)
    simp only [vword_ofVWords _ hi, vword_hi _ _ hi, vword_qVec hi] at mz ⊢
    exact mz
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n8, n9⟩ := hr
    simp only [vpr_writeV, n8, n9, ite_false]

/-- A step of the scaling by `3303`: the row at `[r3 + r5]` times the words of `v4`. -/
theorem sbody_ok {s : State} (ia : InRegions (s.rd ++ s.wr) (s.gpr .r3 + s.gpr .r5) 16)
    (oa : InRegions s.wr (s.gpr .r3 + s.gpr .r5) 16)
    (hx : ∀ i < 4, (vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r5) 16)) i).toNat < 3329)
    (hw : ∀ i < 4, (vword (s.vpr .v4) i).toNat < 3329)
    (hw' : ∀ i < 4, (vword (s.vpr .v5) i).toNat = (vword (s.vpr .v4) i).toNat * 2 ^ 32 / 3329)
    (hq : s.vpr .v0 = qVec) (hc : s.vpr .v1 = ctlHi) :
    WP isa (.block vscaleBody) s fun s' => ∃ A : BitVec 128,
      (∀ i < 4, vword A i = BitVec.ofNat 32
        ((vword (swapDwords (s.mem.read (s.gpr .r3 + s.gpr .r5) 16)) i).toNat * (vword (s.vpr .v4) i).toNat % 3329)) ∧
      s'.mem = s.mem.write (s.gpr .r3 + s.gpr .r5) 16 (swapDwords A) ∧
      s'.gpr .r5 = s.gpr .r5 + 16 ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧ Kept s s' := by
  rw [vscaleBody, WP.block_append_iff, WP.block_append_iff]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_lxvd2x .v7 .r3 .r5 s (by decide) ia, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_⟩
  refine WP.mono (mulZ_ok (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) ?_ ?_) fun s₂ ⟨h8, hv⟩ => ?_
  · simp only [vpr_writeV, ite_true]; have := hx i hi; omega
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hw i hi
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hw' i hi
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hq
  · simp only [vpr_writeV, reduceCtorEq, ite_false]; exact hc
  have g₂ : s₂.gpr = s.gpr := hv.gpr
  have oa' : InRegions s₂.wr (s₂.gpr .r3 + s₂.gpr .r5) 16 := by rw [hv.wr, g₂]; exact oa
  apply WP.of_runBlock
  rw [runBlock_cons, exec_stxvd2x .v8 .r3 .r5 s₂ (by decide) oa', runStep_some, runBlock_cons,
    exec_addi (by decide) (by decide), runStep_some, runBlock_cons, exec_subi (by decide) (by decide), runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, s₂.vpr .v8, fun i hi => ?_, ?_, ?_, ?_, ⟨fun r h5 h6' h10 => ?_,
    fun v n6 n7 n8 n9 n10 => ?_, hv.rd, hv.wr, hv.sp, hv.lr⟩⟩
  · rw [h8 i hi]; simp only [vpr_writeV, reduceCtorEq, ite_true, ite_false]
  · simp only [State.write, hv.mem, g₂, mem_writeV]
  · simp only [RegUpd.gpr_write, g₂, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_write, g₂, ite_true]; rfl
  · simp only [RegUpd.gpr_write, g₂, h5, h10, ite_false]
  · show s₂.vpr v = s.vpr v
    rw [hv.v v (by simp [n8, n9])]
    simp only [vpr_writeV, n7, ite_false]

/-! ## The polynomials -/

section
open VG.Proof.MlKem VG.Spec.MlKem

/-- Four butterflies of a block of the layer with `len`, from `st + t`. -/
theorem group_poly {m : Mem} {F : Addr} {Q : Poly} {len k st t : Nat} (ht : t + 4 ≤ len)
    (hs : st + 2 * len ≤ 256) (h : PolyIs m F (nttBlockN Q len k st t)) {A B : BitVec 128}
    (hA : ∀ p < 4, vword A p = bx (vword (swapDwords (m.read (coeffAddr F (st + t)) 16)) p)
      (vword (swapDwords (m.read (coeffAddr F (st + t + len)) 16)) p) (BitVec.ofNat 32 (zeta k).val))
    (hB : ∀ p < 4, vword B p = by' (vword (swapDwords (m.read (coeffAddr F (st + t)) 16)) p)
      (vword (swapDwords (m.read (coeffAddr F (st + t + len)) 16)) p) (BitVec.ofNat 32 (zeta k).val)) :
    PolyIs ((m.write (coeffAddr F (st + t)) 16 (swapDwords A)).write (coeffAddr F (st + t + len)) 16
      (swapDwords B)) F (nttBlockN Q len k st (t + 4)) := by
  have hl : 0 < len := by omega
  have hs' : st + 2 * len ≤ n := by rw [n_eq]; exact hs
  have g4 := fun i (hi : i < 256) => nttBlockN_get Q (k := k) (t := t + 4) hl ht hs' (i := i) (by rw [n_eq]; exact hi)
  have g0 := fun i (hi : i < 256) => nttBlockN_get Q (k := k) (t := t) hl (by omega) hs' (i := i) (by rw [n_eq]; exact hi)
  refine polyIs_rows h (j₁ := st + t) (j₂ := st + t + len) (by omega) (by omega) (fun p hp => ?_) (fun p hp => ?_)
    (fun i hi r1 r2 => ?_)
  · have l := xor1_lt hp
    rw [hA p hp, row_lane h (by omega) hp, row_lane h (by omega) hp, bx_val]
    simp (disch := omega) only [g4, g0, ↓ite_eq_left, ↓ite_eq_right]
    rw [Nat.add_right_comm (st + t) _ len]
  · have l := xor1_lt hp
    rw [hB p hp, row_lane h (by omega) hp, row_lane h (by omega) hp, by'_val]
    simp (disch := omega) only [g4, g0, ↓ite_eq_left, ↓ite_eq_right]
    rw [show st + t + len + (p ^^^ 1) - len = st + t + (p ^^^ 1) by omega]
  · rw [g4 i hi, g0 i hi]
    have c1 : (st ≤ i ∧ i < st + (t + 4)) ↔ (st ≤ i ∧ i < st + t) := by omega
    have c2 : (st + len ≤ i ∧ i < st + len + (t + 4)) ↔ (st + len ≤ i ∧ i < st + len + t) := by omega
    simp only [c1, c2]

/-- The coefficients of the layer with `len = 2` before block `c`. -/
theorem layer2_old (Q : Poly) {c i : Nat} (hc : c ≤ 64) (h1 : 4 * c ≤ i) (h2 : i < 256) :
    (nttLayerN Q 2 c)[i]! = Q[i]! := by
  rw [nttLayerN_get Q (by decide) (by omega) h2, ite_eq_right (by omega)]

/-- The coefficients of blocks `c` and `c + 1` of the layer with `len = 2`. -/
theorem layer2_new (Q : Poly) {c d : Nat} (hc : c + 2 ≤ 64) (hd : d < 8) :
    (nttLayerN Q 2 (c + 2))[4 * c + d]! =
      if d % 4 < 2 then Q[4 * c + d]! + zeta (64 + c + d / 4) * Q[4 * c + (d + 2)]!
      else Q[4 * c + (d - 2)]! - zeta (64 + c + d / 4) * Q[4 * c + d]! := by
  rw [nttLayerN_get Q (by decide) (by omega) (by omega), ite_eq_left (by omega),
    show (4 * c + d) % (2 * 2) = d % 4 by omega, show 128 / 2 + (4 * c + d) / (2 * 2) = 64 + c + d / 4 by omega]
  split
  · rfl
  · rw [show 4 * c + d - 2 = 4 * c + (d - 2) by omega]

theorem layer2_new0 (Q : Poly) {c : Nat} (hc : c + 2 ≤ 64) :
    (nttLayerN Q 2 (c + 2))[4 * c]! = Q[4 * c]! + zeta (64 + c) * Q[4 * c + 2]! := by
  have := layer2_new Q hc (d := 0) (by decide)
  simpa only [Nat.add_zero, Nat.zero_mod, Nat.zero_div, Nat.zero_add, ite_true, show 0 < 2 by decide] using this

/-- Two blocks of the layer with `len = 2`. -/
theorem pair_poly {m : Mem} {F : Addr} {Q : Poly} {c : Nat} (hc : c + 2 ≤ 64)
    (h : PolyIs m F (nttLayerN Q 2 c)) {Z A B : BitVec 128}
    (hz1 : vword Z 1 = BitVec.ofNat 32 (zeta (64 + c)).val)
    (hz3 : vword Z 3 = BitVec.ofNat 32 (zeta (64 + c + 1)).val)
    (hA : ∀ p < 4, vword A p = if p < 2 then
        bx (vword (swapDwords (m.read (coeffAddr F (4 * c)) 16)) p)
          (vword (swapDwords (m.read (coeffAddr F (4 * c)) 16)) (p + 2)) (vword Z 1)
      else by' (vword (swapDwords (m.read (coeffAddr F (4 * c)) 16)) (p - 2))
          (vword (swapDwords (m.read (coeffAddr F (4 * c)) 16)) p) (vword Z 1))
    (hB : ∀ p < 4, vword B p = if p < 2 then
        bx (vword (swapDwords (m.read (coeffAddr F (4 * c + 4)) 16)) p)
          (vword (swapDwords (m.read (coeffAddr F (4 * c + 4)) 16)) (p + 2)) (vword Z 3)
      else by' (vword (swapDwords (m.read (coeffAddr F (4 * c + 4)) 16)) (p - 2))
          (vword (swapDwords (m.read (coeffAddr F (4 * c + 4)) 16)) p) (vword Z 3)) :
    PolyIs ((m.write (coeffAddr F (4 * c)) 16 (swapDwords A)).write (coeffAddr F (4 * c + 4)) 16
      (swapDwords B)) F (nttLayerN Q 2 (c + 2)) := by
  refine polyIs_rows h (j₁ := 4 * c) (j₂ := 4 * c + 4) (by omega) (by omega) (fun p hp => ?_) (fun p hp => ?_)
    (fun i hi r1 r2 => ?_)
  · rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [hA, hz1, row_lane h, layer2_old, layer2_new, layer2_new0, bx_val, by'_val,
      ↓ite_eq_left, ↓ite_eq_right, Nat.reduceXor, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.add_zero]
  · rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [hB, hz3, row_lane h, layer2_old, layer2_new, bx_val, by'_val, ↓ite_eq_left,
      ↓ite_eq_right, Nat.reduceXor, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.add_zero, Nat.add_assoc]
  · rw [nttLayerN_get Q (by decide) (by omega) hi, nttLayerN_get Q (by decide) (by omega) hi]
    have c1 : i < 2 * 2 * (c + 2) ↔ i < 2 * 2 * c := by omega
    simp only [c1]

end

end VG.Proof.MlKem.PPC64LE.VBfly
