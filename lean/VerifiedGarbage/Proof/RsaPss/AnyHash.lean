module

public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPss.Params

/-!
# RSASSA-PSS, byte by byte, with any two hash functions

`EncBytes.lean`, `SignCases.lean` and `VerifyCases.lean` state signing and
verification a byte at a time for the same hash function `G` as the
digest's and as MGF1's; here, for the digest's hash function `H` and MGF1's
`G`, which may differ: `encodeK_eq`, `sign_zero`, `sign_long`, `sign_eq`,
`verifyEncoding_bytes`, `verify_zero`, `verify_short` and `verify_bytes`,
in the namespace `Any`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Any

open Spec Spec.RsaPss
open Mgf1 (Hash xorBytes mgf1)
open Proof.Mgf1 (Valid xorBytes_length mgf1_length)
open VG.Proof.RsaPss (emT eq_range_map xorBytes_getD clearTop_getD zeros_getD zeros_length db_getD
  getD_app ifp ifn lz dropWhile_lz lz_le getLast?_eq clearTop_eq_iff privateChecked_zero
  publicOpChecked_zero publicOpChecked_length' emLength_eq)

variable (H G : Hash)

/-! ## Signing -/

theorem encodeK_eq (hH : Valid H) (hG : Valid G) {n₀ : Byte} {rest mHash salt : List Byte} (h0 : n₀ ≠ 0)
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

theorem sign_zero (rest eB pB qB dPB dQB qInvB mHash salt : List Byte) :
    sign H G (0 :: rest) eB pB qB dPB dQB qInvB mHash salt = .invalid := by
  unfold sign
  split
  · exact privateChecked_zero ..
  · rfl

theorem sign_long {nB : List Byte} (eB pB qB dPB dQB qInvB mHash salt : List Byte)
    (h : emLength (bitLength (Rsa.os2ip nB) - 1) < H.len + salt.length + 2) :
    sign H G nB eB pB qB dPB dQB qInvB mHash salt = .invalid := by
  simp only [sign, encodeK, encode]
  rw [ifp (Or.inr h)]
  rfl

theorem sign_eq (hH : Valid H) (hG : Valid G) {n₀ : Byte} {rest eB pB qB dPB dQB qInvB mHash salt : List Byte}
    (h0 : n₀ ≠ 0) (hm : mHash.length = H.len) {emBits emLen lo db : Nat}
    (hb : bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hlo : (n₀ :: rest).length - emLen = lo) (hdb : emLen - H.len - 1 = db)
    (hfit : H.len + salt.length + 2 ≤ emLen) :
    sign H G (n₀ :: rest) eB pB qB dPB dQB qInvB mHash salt =
      Rsa.privateChecked (n₀ :: rest) eB ((List.range (n₀ :: rest).length).map
        (emT lo db salt.length salt (H.hash (zeros 8 ++ mHash ++ salt))
          (Mgf1.mgf1 G (H.hash (zeros 8 ++ mHash ++ salt)) db) ((0xFF : Byte) >>> (8 * emLen - emBits))))
        pB qB dPB dQB qInvB := by
  simp only [sign, encodeK_eq H G hH hG h0 hm hb he hlo hdb hfit]

/-! ## Verification -/

/-- `H`, after the `L` octets of `maskedDB`. -/
def vH (em : List Byte) (L : Nat) : List Byte := (em.drop L).take H.len

/-- `DB`: `maskedDB` unmasked, its top `z` bits cleared. -/
def vDb (em : List Byte) (L z : Nat) : List Byte := clearTop z (xorBytes (em.take L) (mgf1 G (vH H em L) L))

/-- What `verifyEncoding` checks, a byte at a time, for `emLen = E`. -/
def EncOk (mHash em : List Byte) (E z : Nat) (sLen : Option Nat) : Prop :=
  em.getD (E - 1) 0 = 0xbc ∧ em.getD 0 0 &&& ~~~((0xFF : Byte) >>> z) = 0 ∧
    lz (vDb H G em (E - H.len - 1) z) < E - H.len - 1 ∧
    (vDb H G em (E - H.len - 1) z).getD (lz (vDb H G em (E - H.len - 1) z)) 0 = 1 ∧
    (sLen = none ∨ sLen = some (E - H.len - 1 - 1 - lz (vDb H G em (E - H.len - 1) z))) ∧
    H.hash (zeros 8 ++ mHash ++ (vDb H G em (E - H.len - 1) z).drop (lz (vDb H G em (E - H.len - 1) z) + 1)) =
      vH H em (E - H.len - 1)

theorem verifyEncoding_bytes (hG : Valid G) {mHash em : List Byte} {emBits : Nat} {sLen : Option Nat}
    (hm : mHash.length = H.len) (hl : em.length = emLength emBits)
    (hfit : H.len + sLen.getD 0 + 2 ≤ emLength emBits) :
    verifyEncoding H G mHash em emBits sLen = true ↔
      EncOk H G mHash em (emLength emBits) (8 * emLength emBits - emBits) sLen := by
  unfold EncOk vDb vH
  generalize hE : emLength emBits = E at *
  generalize hL : E - H.len - 1 = L
  generalize hz : 8 * E - emBits = z
  generalize hh : (em.drop L).take H.len = h
  generalize hdb : clearTop z (xorBytes (em.take L) (mgf1 G h L)) = db
  have hdbl : db.length = L := by
    rw [← hdb, clearTop_length, xorBytes_length, mgf1_length hG]; simp; omega
  have hL0 : 0 < L := by omega
  have hne : em ≠ [] := fun h => by rw [h] at hl; simp at hl; omega
  have h0 : (em.take L).getD 0 0 = em.getD 0 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ifp hL0]
  have hte : em.take L ≠ [] := fun h => by
    have := congrArg List.length h; rw [List.length_take, hl] at this; simp at this; omega
  have hlz := lz_le db
  unfold verifyEncoding
  simp only [hE, hz, hL, hh, hdb]
  rw [ifn (by rw [hm, hl]; omega)]
  by_cases h1 : em.getD (E - 1) 0 = 0xbc
  · rw [ifn (by rw [getLast?_eq hne, hl]; simpa using h1)]
    by_cases h2 : em.getD 0 0 &&& ~~~((0xFF : Byte) >>> z) = 0
    · rw [ifn (by rw [Ne, Decidable.not_not, clearTop_eq_iff z hte, h0]; exact h2)]
      rw [dropWhile_lz]
      split
      · rename_i salt heq
        have hlt : lz db < L := by
          have := congrArg List.length heq; simp at this; omega
        have h4 : db.getD (lz db) 0 = 1 := by
          have := congrArg (·.getD 0 0) heq
          simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
        have hs : salt = db.drop (lz db + 1) := by
          have := congrArg List.tail heq; simpa [List.tail_drop] using this.symm
        subst hs
        have hsl : (db.drop (lz db + 1)).length = L - 1 - lz db := by
          rw [List.length_drop, hdbl]; omega
        simp only [Bool.and_eq_true, beq_iff_eq, hsl, h1, h2, hlt, h4, true_and]
        cases sLen <;> simp only [Option.all_none, Option.all_some, beq_iff_eq, true_and, true_or,
          reduceCtorEq, false_or, Option.some.injEq]
      · rename_i hno
        simp only [Bool.false_eq_true, false_iff, not_and]
        intro _ _ hlt h4
        exfalso
        have hlt' : lz db < db.length := by omega
        refine hno (db.drop (lz db + 1)) ?_
        rw [List.drop_eq_getElem_cons hlt']
        congr 1
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt'] using h4
    · rw [ifp (by rw [Ne, clearTop_eq_iff z hte, h0]; exact h2)]
      simp only [h2, false_and, and_false, Bool.false_eq_true]
  · rw [ifp (by rw [getLast?_eq hne, hl]; simpa using h1)]
    simp only [h1, false_and, Bool.false_eq_true]

/-- A modulus whose first octet is zero verifies nothing. -/
theorem verify_zero (rest eB mHash sB : List Byte) (sLen : Option Nat) :
    verify H G (0 :: rest) eB mHash sB sLen = false := by
  unfold verify
  rw [publicOpChecked_zero]
  simp

/-- Nor does an encoding too short for the digest and the salt. -/
theorem verify_short {nB : List Byte} (eB mHash sB : List Byte) {sLen : Option Nat}
    (h : emLength (bitLength (Rsa.os2ip nB) - 1) < H.len + sLen.getD 0 + 2) :
    verify H G nB eB mHash sB sLen = false := by
  unfold verify
  cases Rsa.publicOpChecked nB eB sB with
  | none => simp
  | some x =>
    have : verifyEncoding H G mHash (x.drop (nB.length - emLength (bitLength (Rsa.os2ip nB) - 1)))
        (bitLength (Rsa.os2ip nB) - 1) sLen = false := by
      unfold verifyEncoding
      rw [ifp (Or.inr (Or.inr h))]
    simp [this]

/-- `verify`, byte by byte, for a modulus whose first octet is not zero and
`emLen = k - lo` octets: of `x`, RSAVP1's result (zeros if it fails), the
first `lo ≤ 1` are zero and the rest is a valid encoding. -/
theorem verify_bytes (hG : Valid G) {n₀ : Byte} {rest eB mHash sB : List Byte} {sLen : Option Nat}
    (hm : mHash.length = H.len) (hs : sB.length = (n₀ :: rest).length) {emBits emLen lo : Nat}
    (hb : bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hk : emLen + lo = (n₀ :: rest).length) (hlo : lo ≤ 1) (hfit : H.len + sLen.getD 0 + 2 ≤ emLen) :
    verify H G (n₀ :: rest) eB mHash sB sLen = true ↔
      (lo = 1 → ((Rsa.publicOpChecked (n₀ :: rest) eB sB).getD (zeros (n₀ :: rest).length)).getD 0 0 = 0) ∧
      EncOk H G mHash (((Rsa.publicOpChecked (n₀ :: rest) eB sB).getD (zeros (n₀ :: rest).length)).drop lo)
        emLen (8 * emLen - emBits) sLen := by
  unfold verify
  simp only [hb, he, hs, beq_self_eq_true, Bool.true_and, show (n₀ :: rest).length - emLen = lo by omega]
  cases hp : Rsa.publicOpChecked (n₀ :: rest) eB sB with
  | none =>
    simp only [Option.getD_none, Bool.false_eq_true, false_iff, not_and]
    intro _ h
    have := h.1
    simp only [zeros, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_replicate] at this
    split at this <;> simp at this
  | some x =>
    have hx := publicOpChecked_length' hp
    simp only [Option.getD_some, Bool.and_eq_true, beq_iff_eq]
    rw [← he, verifyEncoding_bytes H G hG hm (by rw [List.length_drop, hx]; omega) (by omega), he]
    refine and_congr_left fun _ => ?_
    rcases (show lo = 0 ∨ lo = 1 by omega) with rfl | rfl
    · simp [zeros]
    · obtain ⟨b, xs, rfl⟩ := List.exists_cons_of_ne_nil (show x ≠ [] from fun h => by simp [h] at hx)
      simp [zeros]

end VG.Proof.RsaPss.Any
