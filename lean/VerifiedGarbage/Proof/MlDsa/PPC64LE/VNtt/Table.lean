module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Lanes
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.VNtt
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Bfly

/-! # ML-DSA's vector NTT on PPC64LE: the table

Vector `v` of `zetaWords` (`tblVec`): the constants (`tblVec_q`, …), the
splatted `z` and `z'` of block `k` of the layers of `len ≥ 4`
(`tblVec_wide`), and the lane zetas of group `g` (`tblVec_narrow`). -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.VNtt

/-- Vector `v` of the table, as `lxvd2xTbl` loads it. -/
def tblVec (v : Nat) : BitVec 128 := zetaWords.getD (2 * v) 0 ++ zetaWords.getD (2 * v + 1) 0

theorem length_flatMap {α : Type} (f : Nat → List α) {L : Nat} (hf : ∀ k, (f k).length = L) :
    ∀ n, ((List.range n).flatMap f).length = L * n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap f hf n,
      List.flatMap_singleton, hf, Nat.mul_succ]

theorem getD_flatMap {α : Type} (f : Nat → List α) {L : Nat} (hf : ∀ k, (f k).length = L) (d : α) :
    ∀ {n k t : Nat}, k < n → t < L → ((List.range n).flatMap f).getD (L * k + t) d = (f k).getD t d
  | 0, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, t, hk, ht => by
    have hlen := length_flatMap f hf n
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
    by_cases h : k < n
    · have hl : L * k + t < L * n := by
        have := Nat.mul_le_mul_left L (show k + 1 ≤ n by omega); rw [Nat.mul_succ] at this; omega
      rw [hlen, ite_eq_left hl, ← List.getD_eq_getElem?_getD, getD_flatMap f hf d h ht, List.getD_eq_getElem?_getD]
    · have hk' : k = n := by omega
      subst hk'
      rw [hlen, ite_eq_right (by omega), show L * k + t - L * k = t by omega]


/-- The constants, the blocks of `len ≥ 4`, the groups. -/
def constW : List (BitVec 64) :=
  splat q ++ ctl 0 4 2 6 ++ ctl 0 4 1 5 ++ ctl 2 6 3 7 ++ ctl 0 1 4 5 ++ ctl 2 3 6 7

def wideW (k : Nat) : List (BitVec 64) := splat (zeta (k + 1)) ++ splat (shoup (zeta (k + 1)))

def narrowW (g : Nat) : List (BitVec 64) :=
  let z2 := fun r => zeta (64 + 4 * g + r)
  let za := fun r => zeta (128 + 8 * g + 2 * r)
  let zb := fun r => zeta (128 + 8 * g + 2 * r + 1)
  vec4 (z2 0) (z2 1) (z2 2) (z2 3) ++ vec4 (shoup (z2 0)) (shoup (z2 1)) (shoup (z2 2)) (shoup (z2 3)) ++
  vec4 (za 0) (za 1) (za 2) (za 3) ++ vec4 (shoup (za 0)) (shoup (za 1)) (shoup (za 2)) (shoup (za 3)) ++
  vec4 (zb 0) (zb 1) (zb 2) (zb 3) ++ vec4 (shoup (zb 0)) (shoup (zb 1)) (shoup (zb 2)) (shoup (zb 3))

theorem zetaWords_eq : zetaWords = constW ++ (List.range 63).flatMap wideW ++ (List.range 16).flatMap narrowW := rfl

theorem constW_length : constW.length = 12 := rfl
theorem wideW_length (k : Nat) : (wideW k).length = 4 := rfl
theorem narrowW_length (g : Nat) : (narrowW g).length = 12 := by simp [narrowW, vec4]

theorem getD_const {j : Nat} (hj : j < 12) : zetaWords.getD j 0 = constW.getD j 0 := by
  rw [zetaWords_eq, List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [constW_length]; exact hj),
    ← List.getD_eq_getElem?_getD]

theorem getD_wide {k t : Nat} (hk : k < 63) (ht : t < 4) :
    zetaWords.getD (12 + (4 * k + t)) 0 = (wideW k).getD t 0 := by
  rw [zetaWords_eq, List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [constW_length]; omega), constW_length, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [length_flatMap _ wideW_length]; omega), ← List.getD_eq_getElem?_getD,
    getD_flatMap _ wideW_length _ hk ht]

theorem getD_narrow {g t : Nat} (hg : g < 16) (ht : t < 12) :
    zetaWords.getD (264 + (12 * g + t)) 0 = (narrowW g).getD t 0 := by
  rw [zetaWords_eq, List.append_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [constW_length]; omega), constW_length,
    show 264 + (12 * g + t) - 12 = 252 + (12 * g + t) by omega,
    List.getElem?_append_right (by rw [length_flatMap _ wideW_length]; omega), length_flatMap _ wideW_length,
    show 252 + (12 * g + t) - 4 * 63 = 12 * g + t by omega, ← List.getD_eq_getElem?_getD,
    getD_flatMap _ narrowW_length _ hg ht]

/-! ## Lanes of the table's vectors -/

theorem vword_append (x y : BitVec 64) :
    vword (x ++ y) 0 = x.extractLsb' 32 32 ∧ vword (x ++ y) 1 = x.extractLsb' 0 32 ∧
    vword (x ++ y) 2 = y.extractLsb' 32 32 ∧ vword (x ++ y) 3 = y.extractLsb' 0 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro r hr
    simp only [vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hr, decide_true, Bool.true_and]
    split <;> first | omega | exact congrArg _ (by omega)

theorem dw_hi {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) : ((dw a b).extractLsb' 32 32).toNat = a := by
  have h64 : a * 2 ^ 32 + b < 2 ^ 64 := by omega
  rw [BitVec.extractLsb'_toNat, dw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.shiftRight_eq_div_pow]
  omega

theorem dw_lo {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) : ((dw a b).extractLsb' 0 32).toNat = b := by
  have h64 : a * 2 ^ 32 + b < 2 ^ 64 := by omega
  rw [BitVec.extractLsb'_toNat, dw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.shiftRight_zero]
  omega

theorem vword_dw {a b c d : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32) (hd : d < 2 ^ 32) :
    (vword (dw a b ++ dw c d) 0).toNat = a ∧ (vword (dw a b ++ dw c d) 1).toNat = b ∧
    (vword (dw a b ++ dw c d) 2).toNat = c ∧ (vword (dw a b ++ dw c d) 3).toNat = d := by
  obtain ⟨e0, e1, e2, e3⟩ := vword_append (dw a b) (dw c d)
  rw [e0, e1, e2, e3]
  exact ⟨dw_hi ha hb, dw_lo ha hb, dw_hi hc hd, dw_lo hc hd⟩

theorem zeta_lt (m : Nat) : zeta m < Spec.MlDsa.q := Nat.mod_lt _ (by decide)

theorem shoup_lt {z : Nat} (hz : z < Spec.MlDsa.q) : shoup z < 2 ^ 32 := by
  unfold shoup q
  have : z * 2 ^ 32 / 8380417 ≤ z * 2 ^ 32 / 1 := Nat.div_le_div_left (by decide) (by decide)
  have : z * 2 ^ 32 < 8380417 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hz (by decide)
  omega

theorem tbl_const0 : tblVec 0 = dw q q ++ dw q q := by
  rw [tblVec, show 2 * 0 = 0 from rfl, show 0 + 1 = 1 from rfl, getD_const (by decide), getD_const (by decide)]
  exact (by decide : constW.getD 0 0 ++ constW.getD 1 0 = dw q q ++ dw q q)
theorem tbl_const1 : tblVec 1 = hiC := by
  rw [tblVec, show 2 * 1 = 2 from rfl, show 2 + 1 = 3 from rfl, getD_const (by decide), getD_const (by decide)]
  exact (by decide : constW.getD 2 0 ++ constW.getD 3 0 = hiC)

def caC : BitVec 128 := 0x00010203101112130405060714151617#128
def cbC : BitVec 128 := 0x08090a0b18191a1b0c0d0e0f1c1d1e1f#128
def ccC : BitVec 128 := 0x00010203040506071011121314151617#128
def cdC : BitVec 128 := 0x08090a0b0c0d0e0f18191a1b1c1d1e1f#128

theorem tbl_const2 : tblVec 2 = caC := by
  rw [tblVec, show 2 * 2 = 4 from rfl, show 4 + 1 = 5 from rfl, getD_const (by decide), getD_const (by decide)]
  exact (by decide : constW.getD 4 0 ++ constW.getD 5 0 = caC)
theorem tbl_const3 : tblVec 3 = cbC := by
  rw [tblVec, show 2 * 3 = 6 from rfl, show 6 + 1 = 7 from rfl, getD_const (by decide), getD_const (by decide)]
  exact (by decide : constW.getD 6 0 ++ constW.getD 7 0 = cbC)
theorem tbl_const4 : tblVec 4 = ccC := by
  rw [tblVec, show 2 * 4 = 8 from rfl, show 8 + 1 = 9 from rfl, getD_const (by decide), getD_const (by decide)]
  exact (by decide : constW.getD 8 0 ++ constW.getD 9 0 = ccC)
theorem tbl_const5 : tblVec 5 = cdC := by
  rw [tblVec, show 2 * 5 = 10 from rfl, show 10 + 1 = 11 from rfl, getD_const (by decide), getD_const (by decide)]
  exact (by decide : constW.getD 10 0 ++ constW.getD 11 0 = cdC)

theorem lanes_dw {x : Nat} (hx : x < 2 ^ 32) {i : Nat} (hi : i < 4) : (vword (dw x x ++ dw x x) i).toNat = x := by
  obtain ⟨h0, h1, h2, h3⟩ := vword_dw hx hx hx hx
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> assumption

theorem lanes_q {i : Nat} (hi : i < 4) : (vword (tblVec 0) i).toNat = Spec.MlDsa.q := by
  rw [tbl_const0]; exact lanes_dw (by decide) hi

theorem lanes_wide {k : Nat} (hk : k < 63) {i : Nat} (hi : i < 4) :
    (vword (tblVec (6 + 2 * k)) i).toNat = zeta (k + 1) ∧
    (vword (tblVec (6 + 2 * k + 1)) i).toNat = shoup (zeta (k + 1)) := by
  have hz := zeta_lt (k + 1)
  have hz' : zeta (k + 1) < 2 ^ 32 := Nat.lt_trans hz (by decide)
  constructor
  · rw [tblVec, show 2 * (6 + 2 * k) = 12 + (4 * k + 0) by omega, show 12 + (4 * k + 0) + 1 = 12 + (4 * k + 1) by omega,
      getD_wide hk (by decide), getD_wide hk (by decide)]
    exact lanes_dw hz' hi
  · rw [tblVec, show 2 * (6 + 2 * k + 1) = 12 + (4 * k + 2) by omega, show 12 + (4 * k + 2) + 1 = 12 + (4 * k + 3) by omega,
      getD_wide hk (by decide), getD_wide hk (by decide)]
    exact lanes_dw (shoup_lt hz) hi

/-- The lane zetas of group `g`: `len = 2` (`t = 0`), the even pairs of
`len = 1` (`t = 1`), the odd (`t = 2`). -/
def gz (g t r : Nat) : Nat :=
  if t = 0 then zeta (64 + 4 * g + r) else if t = 1 then zeta (128 + 8 * g + 2 * r) else zeta (128 + 8 * g + 2 * r + 1)

theorem lanes_vec4 {f : Nat → Nat} (hf : ∀ r < 4, f r < 2 ^ 32) {i : Nat} (hi : i < 4) :
    (vword (dw (f 0) (f 1) ++ dw (f 2) (f 3)) i).toNat = f i := by
  obtain ⟨h0, h1, h2, h3⟩ := vword_dw (hf 0 (by decide)) (hf 1 (by decide)) (hf 2 (by decide)) (hf 3 (by decide))
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> assumption

theorem lanes_narrow {g t : Nat} (hg : g < 16) (ht : t < 3) {i : Nat} (hi : i < 4) :
    (vword (tblVec (132 + 6 * g + 2 * t)) i).toNat = gz g t i ∧
    (vword (tblVec (132 + 6 * g + 2 * t + 1)) i).toNat = shoup (gz g t i) := by
  have hz : ∀ r, gz g t r < Spec.MlDsa.q := fun r => by unfold gz; split <;> [exact zeta_lt _; split <;> exact zeta_lt _]
  have hz' : ∀ r, gz g t r < 2 ^ 32 := fun r => Nat.lt_trans (hz r) (by decide)
  have e0 : 2 * (132 + 6 * g + 2 * t) = 264 + (12 * g + 4 * t) := by omega
  have e1 : 2 * (132 + 6 * g + 2 * t) + 1 = 264 + (12 * g + (4 * t + 1)) := by omega
  have e2 : 2 * (132 + 6 * g + 2 * t + 1) = 264 + (12 * g + (4 * t + 2)) := by omega
  have e3 : 2 * (132 + 6 * g + 2 * t + 1) + 1 = 264 + (12 * g + (4 * t + 3)) := by omega
  rw [tblVec, tblVec, e3, e2, e1, e0, getD_narrow hg (by omega), getD_narrow hg (by omega),
    getD_narrow hg (by omega), getD_narrow hg (by omega)]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
  · exact ⟨lanes_vec4 (f := fun r => gz g _ r) (fun r _ => hz' r) hi,
      lanes_vec4 (f := fun r => shoup (gz g _ r)) (fun r _ => shoup_lt (hz r)) hi⟩

end VG.Proof.MlDsa.PPC64LE.VNtt
