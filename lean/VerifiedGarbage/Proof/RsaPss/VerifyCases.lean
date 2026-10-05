import VerifiedGarbage.Proof.RsaPss.SignCases

/-!
# RSASSA-PSS verification, byte by byte

`verifyEncoding` holds exactly when the last octet is `0xbc`, `maskedDB`'s
top bits are zero, the first nonzero octet of `DB` (after `lz DB` zeros) is
`0x01`, the salt after it has the expected length, and its `H'` is `H`
(`verifyEncoding_bytes`): what the implementations check, a byte at a time.
-/

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss
open Mgf1 (Hash xorBytes mgf1)
open Proof.Mgf1 (Valid xorBytes_length mgf1_length)

/-- The number of leading zero octets. -/
def lz : List Byte → Nat
  | [] => 0
  | b :: bs => if b = 0 then lz bs + 1 else 0

theorem dropWhile_lz : ∀ l : List Byte, l.dropWhile (· == 0) = l.drop (lz l)
  | [] => rfl
  | b :: bs => by
    rw [List.dropWhile_cons]
    by_cases h : b = 0
    · subst h
      rw [ifp (by decide), dropWhile_lz bs, lz, ifp rfl, List.drop_succ_cons]
    · rw [ifn (by simpa using h), lz, ifn h, List.drop_zero]

theorem lz_le : ∀ l : List Byte, lz l ≤ l.length
  | [] => Nat.le_refl _
  | b :: bs => by
    have := lz_le bs
    simp only [lz, List.length_cons]; split <;> omega

theorem getD_lt_lz : ∀ {l : List Byte} {j : Nat}, j < lz l → l.getD j 0 = 0
  | [], _, h => by simp [lz] at h
  | b :: bs, j, h => by
    by_cases hb : b = 0
    · simp only [lz, hb, ite_true] at h
      cases j with
      | zero => simp [hb]
      | succ j => simpa using getD_lt_lz (l := bs) (by omega)
    · simp only [lz, ifn hb] at h; omega

theorem getD_lz_ne : ∀ {l : List Byte}, lz l < l.length → l.getD (lz l) 0 ≠ 0
  | [], h => by simp at h
  | b :: bs, h => by
    by_cases hb : b = 0
    · simp only [lz, hb, ite_true, List.length_cons] at h ⊢
      simpa using getD_lz_ne (l := bs) (by omega)
    · simp only [lz, ifn hb]; simpa using hb

theorem getLast?_eq {l : List Byte} (hl : l ≠ []) (b : Byte) :
    (l.getLast? ≠ some b) ↔ l.getD (l.length - 1) 0 ≠ b := by
  rw [List.getLast?_eq_some_getLast hl, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by have := List.length_pos_iff.mpr hl; omega), List.getLast_eq_getElem]
  simp

theorem clearTop_eq_iff (z : Nat) {l : List Byte} (hl : l ≠ []) :
    clearTop z l = l ↔ l.getD 0 0 &&& ~~~((0xFF : Byte) >>> z) = 0 := by
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [clearTop, List.cons.injEq, and_true, List.getD_cons_zero]
  constructor
  · intro h
    have := congrArg (· &&& ~~~((0xFF : Byte) >>> z)) h
    simp only [BitVec.and_assoc, BitVec.and_not_self] at this
    exact this.symm.trans BitVec.and_zero
  · intro h
    ext i hi
    have := congrArg (fun x : Byte => x[i]) h
    simp only [BitVec.getElem_and, BitVec.getElem_not] at this
    simp only [BitVec.getElem_and]
    cases hb : b[i] <;> simp_all

variable (G : Hash)

theorem verifyEncoding_bytes (hG : Valid G) {mHash em : List Byte} {emBits : Nat} {sLen : Option Nat}
    (hm : mHash.length = G.len) (hl : em.length = emLength emBits)
    (hfit : G.len + sLen.getD 0 + 2 ≤ emLength emBits) :
    verifyEncoding G G mHash em emBits sLen = true ↔
      em.getD (emLength emBits - 1) 0 = 0xbc ∧
      em.getD 0 0 &&& ~~~((0xFF : Byte) >>> (8 * emLength emBits - emBits)) = 0 ∧
      lz (clearTop (8 * emLength emBits - emBits) (xorBytes (em.take (emLength emBits - G.len - 1))
          (mgf1 G ((em.drop (emLength emBits - G.len - 1)).take G.len) (emLength emBits - G.len - 1)))) <
        emLength emBits - G.len - 1 ∧
      (clearTop (8 * emLength emBits - emBits) (xorBytes (em.take (emLength emBits - G.len - 1))
          (mgf1 G ((em.drop (emLength emBits - G.len - 1)).take G.len) (emLength emBits - G.len - 1)))).getD
        (lz (clearTop (8 * emLength emBits - emBits) (xorBytes (em.take (emLength emBits - G.len - 1))
          (mgf1 G ((em.drop (emLength emBits - G.len - 1)).take G.len) (emLength emBits - G.len - 1))))) 0 = 1 ∧
      (sLen = none ∨ sLen = some (emLength emBits - G.len - 1 - 1 -
        lz (clearTop (8 * emLength emBits - emBits) (xorBytes (em.take (emLength emBits - G.len - 1))
          (mgf1 G ((em.drop (emLength emBits - G.len - 1)).take G.len) (emLength emBits - G.len - 1)))))) ∧
      G.hash (zeros 8 ++ mHash ++ (clearTop (8 * emLength emBits - emBits) (xorBytes
          (em.take (emLength emBits - G.len - 1))
          (mgf1 G ((em.drop (emLength emBits - G.len - 1)).take G.len) (emLength emBits - G.len - 1)))).drop
        (lz (clearTop (8 * emLength emBits - emBits) (xorBytes (em.take (emLength emBits - G.len - 1))
          (mgf1 G ((em.drop (emLength emBits - G.len - 1)).take G.len) (emLength emBits - G.len - 1)))) + 1)) =
        (em.drop (emLength emBits - G.len - 1)).take G.len := by
  generalize hE : emLength emBits = E at *
  generalize hL : E - G.len - 1 = L
  generalize hz : 8 * E - emBits = z
  generalize hh : (em.drop L).take G.len = h
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

end VG.Proof.RsaPss
