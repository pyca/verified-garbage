module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.NttLanes
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Ntt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

/-!
# ML-KEM on PPC64LE: the vector butterfly, word by word

The butterflies of `vbfly` (`Impl/MlKem/PPC64LE/Ntt.lean`) on each word
(`bflyV_lane`): from coefficients `x`, `y` below `q` and a zeta `z` below `q`
with `z' = ⌊z · 2³² / q⌋` (`zetaPrime`), the words of `v6` and `v7` become
`(x + z·y) mod q` and `(x - z·y) mod q`. The product by the zeta is Shoup's
(`shoup_bounds`): `y·z - ⌊y·z' / 2³²⌋·q` is less than `2q`, and `min(v, v - q)`
of a word below `2q` is its remainder (`minq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.VBfly

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Proof.MlKem.PPC64LE.Lanes

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

/-- Shoup's product of a word `y < q` by `w < q`, with `w' = ⌊w · 2³² / q⌋`, reduced. -/
theorem mulZ_word (y w w' : BitVec 32) (hy : y.toNat < 3329) (hw : w.toNat < 3329)
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

theorem vword_qVec {i : Nat} (hi : i < 4) : vword qVec i = Q32 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> decide

/-- The high words of the products gathered in word order. -/
theorem vword_hi (n m : BitVec 128) {i : Nat} (hi : i < 4) :
    vword (perm (mulD 0 n m) (mulD 1 n m) ctlHi) i =
      (BitVec.ofNat 64 ((vword n i).toNat * (vword m i).toNat)).extractLsb' 32 32 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [vword_perm _ _ _ (q := 0) (by decide) (by decide) (by decide), mulD, vword_dwords _ _ (by decide)]; rfl
  · rw [vword_perm _ _ _ (q := 4) (by decide) (by decide) (by decide)]
    simp only [show ¬ (4 : Nat) < 4 by decide, ↓reduceIte, Nat.sub_self, mulD]
    rw [vword_dwords _ _ (by decide)]; rfl
  · rw [vword_perm _ _ _ (q := 2) (by decide) (by decide) (by decide), mulD, vword_dwords _ _ (by decide)]; rfl
  · rw [vword_perm _ _ _ (q := 6) (by decide) (by decide) (by decide)]
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
    have mz := mulZ_word (vword (s.vpr .v7) i) (vword (s.vpr .v4) i) (vword (s.vpr .v5) i) (h.y i hi) (h.w i hi)
      (h.w' i hi)
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

end VG.Proof.MlKem.PPC64LE.VBfly
