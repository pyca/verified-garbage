import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
import VerifiedGarbage.Proof.RsaPss.EncBytes

/-!
# RSASSA-PSS on AArch64: the encoding's bytes

`EM` before the mask (`lo` zeros, `PS`, `0x01`, the salt, `H`, `0xbc`), with
the mask XORed into `DB` (`mixV`) and `DB`'s first byte ANDed with `c`, is
`emT` (`em_view`).
-/

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
  intro i hi
  simp only [upd, mixV, RsaPss.emT, hh]
  by_cases hl : i < lo
  · simp (disch := omega) only [h9, ite_eq_left, ite_eq_right]
  by_cases hz : i = lo
  · subst hz
    by_cases h1 : 0 < db - sl - 1
    · simp (disch := omega) only [h9, ite_eq_left, ite_eq_right, ite_true, Nat.sub_self]
    · simp (disch := omega) only [h9, ite_eq_left, ite_eq_right, ite_true, Nat.sub_self]
  have e1 : oEm + i - (oEm + lo) = i - lo := by omega
  by_cases hj : i - lo < db
  · by_cases hs : db - sl ≤ i - lo
    · simp (disch := omega) only [h9, ite_eq_left, ite_eq_right]
      rw [e1, show oEm + i - (oEm + lo + db - sl) = i - lo - (db - sl) by omega]
    · by_cases ho : i - lo = db - sl - 1
      · simp (disch := omega) only [h9, ite_eq_left, ite_eq_right]
        rw [e1]
      · simp (disch := omega) only [h9, ite_eq_left, ite_eq_right]
        rw [e1]
  · by_cases hH : i - lo < db + D
    · simp (disch := omega) only [h9, ite_eq_left, ite_eq_right]
      rw [show oEm + i - (oEm + lo + db) = i - lo - db by omega]
    · simp (disch := omega) only [h9, ite_eq_left, ite_eq_right]

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
    rw [ite_eq_left ⟨e2, by omega⟩, getD_map_range _ (by omega), ite_eq_left e2]
    simp only [encV8, updL, upd, List.length_replicate]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), hdig _ (by omega)]
  rw [ite_eq_right e2]
  simp only [updL, List.length_map, List.length_range]
  rw [ite_eq_right (by omega)]
  simp only [encV8, updL, upd, List.length_replicate, hsl]
  by_cases e3 : oEm + lo + db - sl ≤ x
  · rw [ite_eq_left ⟨e3, by omega⟩, ite_eq_left e3]
  rw [ite_eq_right (by omega), ite_eq_right e3]
  by_cases e4 : x = oEm + lo + db - sl - 1
  · rw [ite_eq_left e4, ite_eq_left e4]
  rw [ite_eq_right e4, ite_eq_right e4, ite_eq_left ⟨hx1, by omega⟩, List.getD_eq_getElem?_getD,
    List.getElem?_replicate, ite_eq_left (by omega)]
  rfl

theorem encV_seed {V6 : Nat → Byte} {k lo db sl D : Nat} {saltB h : List Byte} (hsl : saltB.length = sl)
    (hk : lo + db + D + 1 = k) (hfit : sl + 1 ≤ db) (hk' : k ≤ 1024) (hD : D ≤ 64) (hh : h.length = D)
    (hdig : ∀ j < D, V6 (oDig + j) = h.getD j 0) :
    (List.range D).map (fun i => encV V6 k lo db sl saltB D (oEm + lo + db + i)) = h := by
  refine (RsaPss.eq_range_map hh fun j hj => ?_).symm
  rw [encV_eq hsl hk hfit hk' hD hdig _ (by omega) (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
    Nat.add_sub_cancel_left]

end VG.Proof.RsaPss.AArch64
