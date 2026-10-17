module

public import VerifiedGarbage.Proof.RsaPss.SignCases
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPss.MgfBytes

/-!
# RSASSA-PSS signing with two hash functions, by cases

`EncBytes.encodeK_eq` and `SignCases`' `sign_zero`, `sign_long` and
`sign_eq` for the hash function `H` and MGF1 with another, `G`
(`encodeK_eq_any`, `sign_zero_any`, `sign_long_any`, `sign_eq_any`).
-/

@[expose] public section

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss
open Mgf1 (Hash xorBytes mgf1)
open Proof.Mgf1 (Valid xorBytes_length mgf1_length)

variable (H G : Hash)

theorem encodeK_eq_any (hH : Valid H) (hG : Valid G) {n₀ : Byte} {rest mHash salt : List Byte} (h0 : n₀ ≠ 0)
    (hm : mHash.length = H.len) {emBits emLen lo db : Nat}
    (hb : bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hlo : (n₀ :: rest).length - emLen = lo) (hdb : emLen - H.len - 1 = db)
    (hfit : H.len + salt.length + 2 ≤ emLen) :
    encodeK H G (n₀ :: rest) mHash salt =
      some ((List.range (n₀ :: rest).length).map
        (emT lo db salt.length salt (H.hash (zeros 8 ++ mHash ++ salt))
          (mgf1 G (H.hash (zeros 8 ++ mHash ++ salt)) db) ((0xFF : Byte) >>> (8 * emLen - emBits)))) := by
  have hEL := emLength_eq rest h0
  rw [hb, he] at hEL
  have hle : emLen ≤ (n₀ :: rest).length := by rw [hEL, List.length_cons]; split <;> omega
  simp only [encodeK, encode, hb, he, hdb, hlo]
  rw [ifn (by omega)]
  simp only [Option.map_some]
  generalize hgen : H.hash (zeros 8 ++ mHash ++ salt) = h
  have hh : h.length = H.len := by rw [← hgen]; exact hH.2 _
  have hmk : (mgf1 G h db).length = db := mgf1_length hG _ _
  have hdbl : (zeros (emLen - salt.length - H.len - 2) ++ 0x01 :: salt).length = db := by
    simp only [List.length_append, zeros_length, List.length_cons]; omega
  have hX : (clearTop (8 * emLen - emBits) (xorBytes (zeros (emLen - salt.length - H.len - 2) ++ 0x01 :: salt)
      (mgf1 G h db))).length = db := by
    rw [clearTop_length, xorBytes_length, hdbl, hmk, Nat.min_self]
  refine congrArg some (eq_range_map ?_ fun i hi => ?_)
  · simp only [List.length_append, zeros_length, hX, hh, List.length_cons, List.length_nil]
    simp only [List.length_cons] at hlo hle; omega
  simp only [List.length_cons] at hi hlo hle
  simp only [emT, getD_app, List.length_append, zeros_length, hX, hh]
  have hlodb : lo + db + H.len + 1 = rest.length + 1 := by omega
  by_cases h1 : i < lo
  · simp only [h1, ↓reduceIte]; exact zeros_getD _ _
  simp only [h1, ↓reduceIte]
  by_cases h2 : i - lo < db
  · have h2' : i - lo < db + H.len := by omega
    simp only [h2, h2', ↓reduceIte, clearTop_getD]
    have hx : ∀ j < db, (xorBytes (zeros (emLen - salt.length - H.len - 2) ++ 1 :: salt) (mgf1 G h db)).getD j 0 =
        (if j < db - salt.length - 1 then 0 else if j = db - salt.length - 1 then 1
          else salt.getD (j - (db - salt.length)) 0) ^^^ (mgf1 G h db).getD j 0 := fun j hj => by
      rw [xorBytes_getD (by rw [hdbl]; exact hj) (by rw [hmk]; exact hj), db_getD,
        show emLen - salt.length - H.len - 2 = db - salt.length - 1 by omega,
        show j - (db - salt.length - 1) - 1 = j - (db - salt.length) by omega]
    by_cases h3 : i - lo = 0
    · simp only [h3, ↓reduceIte]; rw [hx 0 (by omega)]
    · simp only [h3, ↓reduceIte]; rw [hx _ h2]
  · simp only [h2, ↓reduceIte]
    by_cases h4 : i - lo < db + H.len
    · simp only [h4, ↓reduceIte]
    · simp only [h4, ↓reduceIte]
      rw [show i - lo - (db + H.len) = 0 by omega]; rfl

theorem sign_zero_any (rest eB pB qB dPB dQB qInvB mHash salt : List Byte) :
    sign H G (0 :: rest) eB pB qB dPB dQB qInvB mHash salt = .invalid := by
  unfold sign
  split
  · exact privateChecked_zero ..
  · rfl

theorem sign_long_any {nB : List Byte} (eB pB qB dPB dQB qInvB mHash salt : List Byte)
    (h : emLength (bitLength (Rsa.os2ip nB) - 1) < H.len + salt.length + 2) :
    sign H G nB eB pB qB dPB dQB qInvB mHash salt = .invalid := by
  simp only [sign, encodeK, encode]
  rw [ifp (Or.inr h)]
  rfl

theorem sign_eq_any (hH : Valid H) (hG : Valid G) {n₀ : Byte} {rest eB pB qB dPB dQB qInvB mHash salt : List Byte} (h0 : n₀ ≠ 0)
    (hm : mHash.length = H.len) {emBits emLen lo db : Nat}
    (hb : bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hlo : (n₀ :: rest).length - emLen = lo) (hdb : emLen - H.len - 1 = db)
    (hfit : H.len + salt.length + 2 ≤ emLen) :
    sign H G (n₀ :: rest) eB pB qB dPB dQB qInvB mHash salt =
      Rsa.privateChecked (n₀ :: rest) eB ((List.range (n₀ :: rest).length).map
        (emT lo db salt.length salt (H.hash (zeros 8 ++ mHash ++ salt))
          (Mgf1.mgf1 G (H.hash (zeros 8 ++ mHash ++ salt)) db) ((0xFF : Byte) >>> (8 * emLen - emBits))))
        pB qB dPB dQB qInvB := by
  simp only [sign, encodeK_eq_any H G hH hG h0 hm hb he hlo hdb hfit]

end VG.Proof.RsaPss
