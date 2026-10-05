import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.CtPad

/-!
# EMSA-PSS: the encoding, a byte at a time

For a modulus `n₀ ‖ rest` (`n₀ ≠ 0`, so `k - emLen` is `lo = [n₀ = 1]`),
`encodeK` is the `k` bytes `emT …` (`encodeK_eq`): `lo` zeros, then
`maskedDB` (`DB ⊕ mask`, its first byte ANDed with `0xFF >>> z`), `H` and
`0xbc`, byte by byte as the implementations write them.
-/

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss
open Mgf1 (Hash xorBytes mgf1)
open Proof.Mgf1 (Valid xorBytes_length mgf1_length)

/-- Byte `i` of `zeros lo ‖ maskedDB ‖ H ‖ 0xbc`, with `DB` of `db` bytes ending
with `0x01` and the `sl` bytes of `salt`, `mk` the mask, and `c` the mask of
`maskedDB`'s first byte. -/
def emT (lo db sl : Nat) (salt h mk : List Byte) (c : Byte) (i : Nat) : Byte :=
  if i < lo then 0
  else if i - lo < db then
    let d : Byte := if i - lo < db - sl - 1 then 0 else if i - lo = db - sl - 1 then 1
      else salt.getD (i - lo - (db - sl)) 0
    if i - lo = 0 then (d ^^^ mk.getD (i - lo) 0) &&& c else d ^^^ mk.getD (i - lo) 0
  else if i - lo < db + h.length then h.getD (i - lo - db) 0 else 0xbc

theorem eq_range_map {l : List Byte} {n : Nat} {f : Nat → Byte} (hl : l.length = n)
    (h : ∀ i < n, l.getD i 0 = f i) : l = (List.range n).map f := by
  apply List.ext_getElem (by simp [hl])
  intro i h₁ h₂
  rw [List.getElem_map, List.getElem_range, ← h i (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h₁]
  rfl

theorem xorBytes_getD {a b : List Byte} {i : Nat} (ha : i < a.length) (hb : i < b.length) :
    (xorBytes a b).getD i 0 = a.getD i 0 ^^^ b.getD i 0 := by
  simp only [xorBytes, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem ha,
    List.getElem?_eq_getElem hb]
  rfl

theorem clearTop_getD (z : Nat) (l : List Byte) (i : Nat) :
    (clearTop z l).getD i 0 = if i = 0 then l.getD 0 0 &&& ((0xFF : Byte) >>> z) else l.getD i 0 := by
  cases l with
  | nil => split <;> simp [clearTop]
  | cons b bs =>
    cases i with
    | zero => simp [clearTop]
    | succ i => simp [clearTop]

theorem zeros_getD (n i : Nat) : (zeros n).getD i 0 = 0 := by
  simp only [zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem zeros_length (n : Nat) : (zeros n).length = n := List.length_replicate

theorem db_getD (p : Nat) (salt : List Byte) (j : Nat) :
    (zeros p ++ 0x01 :: salt).getD j 0 = if j < p then 0 else if j = p then 1 else salt.getD (j - p - 1) 0 := by
  rw [getD_app]
  simp only [zeros_length]
  split
  · exact zeros_getD p j
  · rename_i h
    by_cases hj : j = p
    · subst hj; simp
    · rw [ifn hj, show j - p = (j - p - 1) + 1 by omega]
      simp

variable (G : Hash)

theorem encodeK_eq (hG : Valid G) {n₀ : Byte} {rest mHash salt : List Byte} (h0 : n₀ ≠ 0)
    (hm : mHash.length = G.len) {emBits emLen lo db : Nat}
    (hb : bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hlo : (n₀ :: rest).length - emLen = lo) (hdb : emLen - G.len - 1 = db)
    (hfit : G.len + salt.length + 2 ≤ emLen) :
    encodeK G G (n₀ :: rest) mHash salt =
      some ((List.range (n₀ :: rest).length).map
        (emT lo db salt.length salt (G.hash (zeros 8 ++ mHash ++ salt))
          (mgf1 G (G.hash (zeros 8 ++ mHash ++ salt)) db) ((0xFF : Byte) >>> (8 * emLen - emBits)))) := by
  have hEL := emLength_eq rest h0
  rw [hb, he] at hEL
  have hle : emLen ≤ (n₀ :: rest).length := by rw [hEL, List.length_cons]; split <;> omega
  simp only [encodeK, encode, hb, he, hdb, hlo]
  rw [ifn (by omega)]
  simp only [Option.map_some]
  generalize hgen : G.hash (zeros 8 ++ mHash ++ salt) = h
  have hh : h.length = G.len := by rw [← hgen]; exact hG.2 _
  have hmk : (mgf1 G h db).length = db := mgf1_length hG _ _
  have hdbl : (zeros (emLen - salt.length - G.len - 2) ++ 0x01 :: salt).length = db := by
    simp only [List.length_append, zeros_length, List.length_cons]; omega
  have hX : (clearTop (8 * emLen - emBits) (xorBytes (zeros (emLen - salt.length - G.len - 2) ++ 0x01 :: salt)
      (mgf1 G h db))).length = db := by
    rw [clearTop_length, xorBytes_length, hdbl, hmk, Nat.min_self]
  refine congrArg some (eq_range_map ?_ fun i hi => ?_)
  · simp only [List.length_append, zeros_length, hX, hh, List.length_cons, List.length_nil]
    simp only [List.length_cons] at hlo hle; omega
  simp only [List.length_cons] at hi hlo hle
  simp only [emT, getD_app, List.length_append, zeros_length, hX, hh]
  have hlodb : lo + db + G.len + 1 = rest.length + 1 := by omega
  by_cases h1 : i < lo
  · simp only [h1, ↓reduceIte]; exact zeros_getD _ _
  simp only [h1, ↓reduceIte]
  by_cases h2 : i - lo < db
  · have h2' : i - lo < db + G.len := by omega
    simp only [h2, h2', ↓reduceIte, clearTop_getD]
    have hx : ∀ j < db, (xorBytes (zeros (emLen - salt.length - G.len - 2) ++ 1 :: salt) (mgf1 G h db)).getD j 0 =
        (if j < db - salt.length - 1 then 0 else if j = db - salt.length - 1 then 1
          else salt.getD (j - (db - salt.length)) 0) ^^^ (mgf1 G h db).getD j 0 := fun j hj => by
      rw [xorBytes_getD (by rw [hdbl]; exact hj) (by rw [hmk]; exact hj), db_getD,
        show emLen - salt.length - G.len - 2 = db - salt.length - 1 by omega,
        show j - (db - salt.length - 1) - 1 = j - (db - salt.length) by omega]
    by_cases h3 : i - lo = 0
    · simp only [h3, ↓reduceIte]; rw [hx 0 (by omega)]
    · simp only [h3, ↓reduceIte]; rw [hx _ h2]
  · simp only [h2, ↓reduceIte]
    by_cases h4 : i - lo < db + G.len
    · simp only [h4, ↓reduceIte]
    · simp only [h4, ↓reduceIte]
      rw [show i - lo - (db + G.len) = 0 by omega]; rfl

end VG.Proof.RsaPss
