module

public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS on AArch64: the encoding's bytes

`EM` before the mask (`lo` zeros, `PS`, `0x01`, the salt, `H`, `0xbc`), with
the mask XORed into `DB` (`mixV`) and `DB`'s first byte ANDed with `c`, is
`emT` (`em_view`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.Impl.RsaPss.AArch64

theorem em_view {V9 : Nat → Byte} {k lo db sl D : Nat} {h saltB mk : List Byte} {c : Byte}
    (hh : h.length = D) (hk : lo + db + D + 1 = k) (hfit : sl + 1 ≤ db)
    (h9 : ∀ x, oEm ≤ x → x < oEm + k → V9 x =
      if x = oEm + k - 1 then 0xbc
      else if oEm + lo + db ≤ x then h.getD (x - (oEm + lo + db)) 0
      else if oEm + lo + db - sl ≤ x then saltB.getD (x - (oEm + lo + db - sl)) 0
      else if x = oEm + lo + db - sl - 1 then 1 else 0) :
    ∀ i < k, upd (mixV V9 mk (oEm + lo) db) (oEm + lo) (mixV V9 mk (oEm + lo) db (oEm + lo) &&& c) (oEm + i) =
      RsaPss.emT lo db sl saltB h mk c i := by
  generalize hS : oEm + lo + db - sl = S at h9
  generalize hK : oEm + k - 1 = K at h9
  have c0 : oEm = 2560 := rfl
  have hS' : S + sl = oEm + lo + db := by rw [← hS]; omega_using [hfit, c0]
  have hK' : K + 1 = oEm + k := by rw [← hK]; omega_using [hk, c0]
  clear hS hK
  intro i hi
  have hx₁ : oEm ≤ oEm + i := Nat.le_add_right _ _
  have hx₂ : oEm + i < oEm + k := Nat.add_lt_add_left hi _
  simp only [upd, mixV, RsaPss.emT, hh]
  by_cases hl : i < lo
  · rw [ite_eq_right (show ¬oEm + i = oEm + lo by omega_using [hl]),
      ite_eq_right (show ¬(oEm + lo ≤ oEm + i ∧ oEm + i < oEm + lo + db) by omega_using [hl]), ite_eq_left hl,
      h9 _ hx₁ hx₂, ite_eq_right (show ¬oEm + i = K by omega_using [hl, hk, hK']),
      ite_eq_right (show ¬oEm + lo + db ≤ oEm + i by omega_using [hl]),
      ite_eq_right (show ¬S ≤ oEm + i by omega_using [hl, hfit, hS']),
      ite_eq_right (show ¬oEm + i = S - 1 by omega_using [hl, hfit, hS'])]
  rw [ite_eq_right hl]
  by_cases hz : i = lo
  · subst hz
    rw [ite_eq_left rfl, ite_eq_left (show oEm + i ≤ oEm + i ∧ oEm + i < oEm + i + db by omega_using [hfit]), Nat.sub_self,
      Nat.sub_self, ite_eq_left (show 0 < db by omega_using [hfit]), ite_eq_left rfl, h9 _ hx₁ hx₂,
      ite_eq_right (show ¬oEm + i = K by omega_using [hk, hK', hfit]),
      ite_eq_right (show ¬oEm + i + db ≤ oEm + i by omega_using [hfit]),
      ite_eq_right (show ¬S ≤ oEm + i by omega_using [hfit, hS'])]
    by_cases h1 : 0 < db - sl - 1
    · rw [ite_eq_right (show ¬oEm + i = S - 1 by omega_using [h1, hS']), ite_eq_left h1]
    · rw [ite_eq_left (show oEm + i = S - 1 by omega_using [h1, hfit, hS']), ite_eq_right h1,
        ite_eq_left (show 0 = db - sl - 1 by omega_using [h1, hfit])]
  have e1 : oEm + i - (oEm + lo) = i - lo := Nat.add_sub_add_left _ _ _
  rw [ite_eq_right (show ¬oEm + i = oEm + lo by omega_using [hz]), e1,
    ite_eq_right (show ¬i - lo = 0 by omega_using [hl, hz])]
  by_cases hj : i - lo < db
  · rw [ite_eq_left (show oEm + lo ≤ oEm + i ∧ oEm + i < oEm + lo + db by omega_using [hl, hj]), ite_eq_left hj,
      h9 _ hx₁ hx₂, ite_eq_right (show ¬oEm + i = K by omega_using [hl, hj, hk, hK']),
      ite_eq_right (show ¬oEm + lo + db ≤ oEm + i by omega_using [hl, hj])]
    by_cases hs : db - sl ≤ i - lo
    · rw [ite_eq_left (show S ≤ oEm + i by omega_using [hl, hs, hfit, hS']),
        ite_eq_right (show ¬i - lo < db - sl - 1 by omega_using [hs]),
        ite_eq_right (show ¬i - lo = db - sl - 1 by omega_using [hs, hfit]),
        show oEm + i - S = i - lo - (db - sl) by omega_using [hl, hs, hfit, hS']]
    rw [ite_eq_right (show ¬S ≤ oEm + i by omega_using [hl, hs, hfit, hS'])]
    by_cases ho : i - lo = db - sl - 1
    · rw [ite_eq_left (show oEm + i = S - 1 by omega_using [hl, ho, hfit, hS']),
        ite_eq_right (show ¬i - lo < db - sl - 1 by omega_using [ho]), ite_eq_left ho]
    · rw [ite_eq_right (show ¬oEm + i = S - 1 by omega_using [hl, ho, hfit, hS']),
        ite_eq_left (show i - lo < db - sl - 1 by omega_using [hl, hs, ho, hfit])]
  rw [ite_eq_right (show ¬(oEm + lo ≤ oEm + i ∧ oEm + i < oEm + lo + db) by omega_using [hj]), ite_eq_right hj,
    h9 _ hx₁ hx₂]
  by_cases hH : i - lo < db + D
  · rw [ite_eq_right (show ¬oEm + i = K by omega_using [hl, hH, hk, hK']),
      ite_eq_left (show oEm + lo + db ≤ oEm + i by omega_using [hl, hj]), ite_eq_left hH,
      show oEm + i - (oEm + lo + db) = i - lo - db by omega_using [hl, hj]]
  · rw [ite_eq_left (show oEm + i = K by omega_using [hl, hH, hi, hk, hK']), ite_eq_right hH]

/-- Our working space after `clearEm`, `putSalt` and `putH`, from `V6`
(with `H` at `oDig`). -/
def encV8 (V6 : Nat → Byte) (k lo db sl : Nat) (saltB : List Byte) : Nat → Byte :=
  updL (upd (updL V6 oEm (List.replicate k 0)) (oEm + lo + db - sl - 1) 1) (oEm + lo + db - sl) saltB

def encV (V6 : Nat → Byte) (k lo db sl : Nat) (saltB : List Byte) (D : Nat) : Nat → Byte :=
  upd (updL (encV8 V6 k lo db sl saltB) (oEm + lo + db) ((List.range D).map fun i =>
    encV8 V6 k lo db sl saltB (oDig + i))) (oEm + k - 1) 0xbc

theorem getD_map_range (f : Nat → Byte) {n i : Nat} (h : i < n) : ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem encV_eq {V6 : Nat → Byte} {k lo db sl D : Nat} {saltB h : List Byte} (hsl : saltB.length = sl)
    (hk : lo + db + D + 1 = k) (hfit : sl + 1 ≤ db) (hk' : k ≤ 1024) (hD : D ≤ 64)
    (hdig : ∀ j < D, V6 (oDig + j) = h.getD j 0) :
    ∀ x, oEm ≤ x → x < oEm + k → encV V6 k lo db sl saltB D x =
      if x = oEm + k - 1 then 0xbc
      else if oEm + lo + db ≤ x then h.getD (x - (oEm + lo + db)) 0
      else if oEm + lo + db - sl ≤ x then saltB.getD (x - (oEm + lo + db - sl)) 0
      else if x = oEm + lo + db - sl - 1 then 1 else 0 := by
  have c1 : oEm = 2560 := rfl
  have c3 : oDig = 2304 := rfl
  intro x hx1 hx2
  simp only [encV, upd]
  by_cases e1 : x = oEm + k - 1
  · rw [ite_eq_left e1, ite_eq_left e1]
  rw [ite_eq_right e1, ite_eq_right e1]
  by_cases e2 : oEm + lo + db ≤ x
  · simp only [updL, List.length_map, List.length_range]
    rw [ite_eq_left ⟨e2, by omega_arith⟩, getD_map_range _ (by omega_arith), ite_eq_left e2]
    simp only [encV8, updL, upd, List.length_replicate]
    rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), hdig _ (by omega_arith)]
  rw [ite_eq_right e2]
  simp only [updL, List.length_map, List.length_range]
  rw [ite_eq_right (by omega_arith)]
  simp only [encV8, updL, upd, List.length_replicate, hsl]
  by_cases e3 : oEm + lo + db - sl ≤ x
  · rw [ite_eq_left ⟨e3, by omega_arith⟩, ite_eq_left e3]
  rw [ite_eq_right (by omega_arith), ite_eq_right e3]
  by_cases e4 : x = oEm + lo + db - sl - 1
  · rw [ite_eq_left e4, ite_eq_left e4]
  rw [ite_eq_right e4, ite_eq_right e4, ite_eq_left ⟨hx1, by omega_arith⟩, List.getD_eq_getElem?_getD,
    List.getElem?_replicate, ite_eq_left (by omega_arith)]
  rfl

theorem encV_seed {V6 : Nat → Byte} {k lo db sl D : Nat} {saltB h : List Byte} (hsl : saltB.length = sl)
    (hk : lo + db + D + 1 = k) (hfit : sl + 1 ≤ db) (hk' : k ≤ 1024) (hD : D ≤ 64) (hh : h.length = D)
    (hdig : ∀ j < D, V6 (oDig + j) = h.getD j 0) :
    (List.range D).map (fun i => encV V6 k lo db sl saltB D (oEm + lo + db + i)) = h := by
  refine (RsaPss.eq_range_map hh fun j hj => ?_).symm
  rw [encV_eq hsl hk hfit hk' hD hdig _ (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left (by omega_arith),
    Nat.add_sub_cancel_left]

end VG.Proof.RsaPss.AArch64
