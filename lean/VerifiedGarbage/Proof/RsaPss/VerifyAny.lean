module

public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.RsaPss.Params

/-!
# RSASSA-PSS verification, byte by byte, with two hash functions

`VerifyCases.lean`'s lemmas for `verify H G`: `H` the digest's, whose
`hLen` octets end the encoding, and `G` MGF1's.
-/

@[expose] public section

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss
open Mgf1 (Hash xorBytes mgf1)
open Proof.Mgf1 (Valid xorBytes_length mgf1_length)

variable (H G : Hash)

/-- `H`, after the `L` octets of `maskedDB`. -/
def vH₂ (em : List Byte) (L : Nat) : List Byte := (em.drop L).take H.len

/-- `DB`: `maskedDB` unmasked, its top `z` bits cleared. -/
def vDb₂ (em : List Byte) (L z : Nat) : List Byte := clearTop z (xorBytes (em.take L) (mgf1 G (vH₂ H em L) L))

/-- What `verifyEncoding` checks, a byte at a time, for `emLen = E`. -/
def EncOk₂ (mHash em : List Byte) (E z : Nat) (sLen : Option Nat) : Prop :=
  em.getD (E - 1) 0 = 0xbc ∧ em.getD 0 0 &&& ~~~((0xFF : Byte) >>> z) = 0 ∧
    lz (vDb₂ H G em (E - H.len - 1) z) < E - H.len - 1 ∧
    (vDb₂ H G em (E - H.len - 1) z).getD (lz (vDb₂ H G em (E - H.len - 1) z)) 0 = 1 ∧
    (sLen = none ∨ sLen = some (E - H.len - 1 - 1 - lz (vDb₂ H G em (E - H.len - 1) z))) ∧
    H.hash (zeros 8 ++ mHash ++ (vDb₂ H G em (E - H.len - 1) z).drop (lz (vDb₂ H G em (E - H.len - 1) z) + 1)) =
      vH₂ H em (E - H.len - 1)

theorem verifyEncoding_bytes₂ (hG : Valid G) {mHash em : List Byte} {emBits : Nat} {sLen : Option Nat}
    (hm : mHash.length = H.len) (hl : em.length = emLength emBits)
    (hfit : H.len + sLen.getD 0 + 2 ≤ emLength emBits) :
    verifyEncoding H G mHash em emBits sLen = true ↔
      EncOk₂ H G mHash em (emLength emBits) (8 * emLength emBits - emBits) sLen := by
  unfold EncOk₂ vDb₂ vH₂
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
theorem verify_zero₂ (rest eB mHash sB : List Byte) (sLen : Option Nat) :
    verify H G (0 :: rest) eB mHash sB sLen = false := by
  unfold verify
  rw [publicOpChecked_zero]
  simp

/-- Nor does an encoding too short for the digest and the salt. -/
theorem verify_short₂ {nB : List Byte} (eB mHash sB : List Byte) {sLen : Option Nat}
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
theorem verify_bytes₂ (hG : Valid G) {n₀ : Byte} {rest eB mHash sB : List Byte} {sLen : Option Nat}
    (hm : mHash.length = H.len) (hs : sB.length = (n₀ :: rest).length) {emBits emLen lo : Nat}
    (hb : bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hk : emLen + lo = (n₀ :: rest).length) (hlo : lo ≤ 1) (hfit : H.len + sLen.getD 0 + 2 ≤ emLen) :
    verify H G (n₀ :: rest) eB mHash sB sLen = true ↔
      (lo = 1 → ((Rsa.publicOpChecked (n₀ :: rest) eB sB).getD (zeros (n₀ :: rest).length)).getD 0 0 = 0) ∧
      EncOk₂ H G mHash (((Rsa.publicOpChecked (n₀ :: rest) eB sB).getD (zeros (n₀ :: rest).length)).drop lo)
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
    rw [← he, verifyEncoding_bytes₂ H G hG hm (by rw [List.length_drop, hx]; omega) (by omega), he]
    refine and_congr_left fun _ => ?_
    rcases (show lo = 0 ∨ lo = 1 by omega) with rfl | rfl
    · simp [zeros]
    · obtain ⟨b, xs, rfl⟩ := List.exists_cons_of_ne_nil (show x ≠ [] from fun h => by simp [h] at hx)
      simp [zeros]

end VG.Proof.RsaPss
