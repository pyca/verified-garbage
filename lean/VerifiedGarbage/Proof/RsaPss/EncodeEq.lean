module

public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# EMSA-PSS: the encoding, a byte at a time, without a modulus

`encode` is the `emLen` bytes `emT 0 …` (`encode_eq`), when the salt fits,
and `none` otherwise (`encode_none`): `encodeK_eq` for `lo = 0`, from
`emBits` rather than a modulus.
-/

@[expose] public section

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss
open Mgf1 (Hash xorBytes mgf1)
open Proof.Mgf1 (Valid xorBytes_length mgf1_length)

variable (G : Hash)

theorem encode_none {mHash salt : List Byte} {emBits : Nat}
    (h : emLength emBits < G.len + salt.length + 2) : encode G G mHash salt emBits = none := by
  simp only [encode]
  rw [ifp (Or.inr h)]

theorem encode_eq (hG : Valid G) {mHash salt : List Byte} (hm : mHash.length = G.len) {emBits emLen db : Nat}
    (he : emLength emBits = emLen) (hdb : emLen - G.len - 1 = db) (hfit : G.len + salt.length + 2 ≤ emLen) :
    encode G G mHash salt emBits =
      some ((List.range emLen).map
        (emT 0 db salt.length salt (G.hash (zeros 8 ++ mHash ++ salt))
          (mgf1 G (G.hash (zeros 8 ++ mHash ++ salt)) db) ((0xFF : Byte) >>> (8 * emLen - emBits)))) := by
  simp only [encode, he, hdb]
  rw [ifn (by omega_arith)]
  generalize hgen : G.hash (zeros 8 ++ mHash ++ salt) = h
  have hh : h.length = G.len := by rw [← hgen]; exact hG.2 _
  have hmk : (mgf1 G h db).length = db := mgf1_length hG _ _
  have hdbl : (zeros (emLen - salt.length - G.len - 2) ++ 0x01 :: salt).length = db := by
    simp only [List.length_append, zeros_length, List.length_cons]; omega_arith
  have hX : (clearTop (8 * emLen - emBits) (xorBytes (zeros (emLen - salt.length - G.len - 2) ++ 0x01 :: salt)
      (mgf1 G h db))).length = db := by
    rw [clearTop_length, xorBytes_length, hdbl, hmk, Nat.min_self]
  refine congrArg some (eq_range_map ?_ fun i hi => ?_)
  · simp only [List.length_append, hX, hh, List.length_cons, List.length_nil]; omega_arith
  simp only [emT, getD_app, List.length_append, hX, hh, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  by_cases h2 : i < db
  · have h2' : i < db + G.len := by omega_arith
    simp only [h2, h2', ↓reduceIte, clearTop_getD]
    have hx : ∀ j < db, (xorBytes (zeros (emLen - salt.length - G.len - 2) ++ 1 :: salt) (mgf1 G h db)).getD j 0 =
        (if j < db - salt.length - 1 then 0 else if j = db - salt.length - 1 then 1
          else salt.getD (j - (db - salt.length)) 0) ^^^ (mgf1 G h db).getD j 0 := fun j hj => by
      rw [xorBytes_getD (by rw [hdbl]; exact hj) (by rw [hmk]; exact hj), db_getD,
        show emLen - salt.length - G.len - 2 = db - salt.length - 1 by omega_arith,
        show j - (db - salt.length - 1) - 1 = j - (db - salt.length) by omega_arith]
    by_cases h3 : i = 0
    · simp only [h3, ↓reduceIte]; rw [hx 0 (by omega_arith)]
    · simp only [h3, ↓reduceIte]; rw [hx _ h2]
  · simp only [h2, ↓reduceIte]
    by_cases h4 : i < db + G.len
    · simp only [h4, ↓reduceIte]
    · simp only [h4, ↓reduceIte]
      rw [show i - (db + G.len) = 0 by omega_arith]; rfl

end VG.Proof.RsaPss
