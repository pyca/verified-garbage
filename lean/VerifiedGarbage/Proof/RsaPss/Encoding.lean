import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.Proof.Mgf1.Basic

/-!
# EMSA-PSS: verification accepts exactly the encodings

For hash functions whose digests are `hLen > 0` octets (`Mgf1.Valid`),
`EMSA-PSS-VERIFY` (with BoringSSL's step 10) accepts an encoding exactly
when it is `EMSA-PSS-ENCODE` of the digest with some salt of the expected
length (`verifyEncoding_iff`): every encoding verifies (the round trip,
`verifyEncoding_encode`), and nothing else does.
-/

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss

open Mgf1 (Hash xorBytes mgf1)
open Proof.Mgf1 (Valid xorBytes_length xorBytes_xorBytes mgf1_length)

/-! ## Clearing the leftmost bits -/

theorem clearTop_length (z : Nat) : ∀ bs : List Byte, (clearTop z bs).length = bs.length
  | [] => rfl
  | _ :: _ => rfl

theorem byte_and_xor_and (x m c : Byte) : ((x &&& c) ^^^ m) &&& c = (x ^^^ m) &&& c := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor]
  cases x[i] <;> cases m[i] <;> cases c[i] <;> rfl

theorem clearTop_xorBytes_clearTop (z : Nat) (a b : List Byte) :
    clearTop z (xorBytes (clearTop z a) b) = clearTop z (xorBytes a b) := by
  cases a <;> cases b <;> simp [clearTop, xorBytes, byte_and_xor_and]

/-- `DB`'s leftmost bits are zero: it starts with a zero octet, or with
`0x01`, and `z ≤ 7`. -/
theorem clearTop_db {z : Nat} (hz : z ≤ 7) (p : Nat) (salt : List Byte) :
    clearTop z (zeros p ++ 0x01 :: salt) = zeros p ++ 0x01 :: salt := by
  cases p with
  | zero =>
    have : ∀ z < 8, (0x01 : Byte) &&& ((0xFF : Byte) >>> z) = 0x01 := by decide
    simp only [zeros, List.replicate_zero, List.nil_append, clearTop]
    rw [this z (by omega)]
  | succ p => simp [zeros, List.replicate_succ, clearTop]

/-! ## Finding the salt -/

theorem dropWhile_db (p : Nat) (salt : List Byte) :
    (zeros p ++ 0x01 :: salt).dropWhile (· == 0) = 0x01 :: salt := by
  induction p with
  | zero => simp [zeros]
  | succ p ih => simp [zeros, List.replicate_succ] at ih ⊢

/-- An octet string whose first nonzero octet is `0x01`, followed by `salt`,
is zeros, `0x01` and `salt`. -/
theorem eq_db {db salt : List Byte} (h : db.dropWhile (· == 0) = 0x01 :: salt) :
    db = zeros (db.length - salt.length - 1) ++ 0x01 :: salt := by
  have hz : db.takeWhile (· == 0) = zeros (db.takeWhile (· == 0)).length := by
    apply List.eq_replicate_iff.mpr
    refine ⟨rfl, fun b hb => ?_⟩
    simpa using List.all_eq_true.mp List.all_takeWhile b hb
  have hd := List.takeWhile_append_dropWhile (p := (· == (0 : Byte))) (l := db)
  rw [h, hz] at hd
  have hl := congrArg List.length hd
  simp only [zeros, List.length_append, List.length_replicate, List.length_cons] at hl
  rw [← hd]
  simp only [zeros, List.length_append, List.length_replicate, List.length_cons]
  congr 2
  omega

/-! ## The round trip -/

variable {H G : Hash}

theorem clearTop_clearTop (z : Nat) : ∀ bs : List Byte, clearTop z (clearTop z bs) = clearTop z bs
  | [] => rfl
  | b :: bs => by simp [clearTop, BitVec.and_assoc]

theorem db_length (p : Nat) (salt : List Byte) :
    (zeros p ++ 0x01 :: salt).length = p + salt.length + 1 := by
  simp [zeros]; omega

/-- Every encoding verifies, with its salt's length or with any. -/
theorem verifyEncoding_encode (hH : Valid H) (hG : Valid G) {mHash salt em : List Byte}
    {emBits : Nat} {sLen : Option Nat} (he : encode H G mHash salt emBits = some em)
    (hs : sLen = none ∨ sLen = some salt.length) :
    verifyEncoding H G mHash em emBits sLen = true := by
  unfold encode at he
  dsimp only at he
  split at he
  · cases he
  rename_i hc
  simp only [not_or, Decidable.not_not, Nat.not_lt] at hc
  obtain ⟨hm, hlen⟩ := hc
  cases he
  have hz : 8 * emLength emBits - emBits ≤ 7 := by unfold emLength; omega
  have hh := hH.2 (zeros 8 ++ mHash ++ salt)
  have hmask := mgf1_length hG (H.hash (zeros 8 ++ mHash ++ salt)) (emLength emBits - H.len - 1)
  have hdb := db_length (emLength emBits - salt.length - H.len - 2) salt
  have hx := xorBytes_length (zeros (emLength emBits - salt.length - H.len - 2) ++ 0x01 :: salt)
    (mgf1 G (H.hash (zeros 8 ++ mHash ++ salt)) (emLength emBits - H.len - 1))
  generalize hmasked : clearTop (8 * emLength emBits - emBits) (xorBytes
    (zeros (emLength emBits - salt.length - H.len - 2) ++ 0x01 :: salt)
    (mgf1 G (H.hash (zeros 8 ++ mHash ++ salt)) (emLength emBits - H.len - 1))) = maskedDB
  have hml : maskedDB.length = emLength emBits - H.len - 1 := by
    rw [← hmasked, clearTop_length, hx, hdb, hmask]; omega
  generalize hhd : H.hash (zeros 8 ++ mHash ++ salt) = h at hh hmask hx hmasked ⊢
  generalize hdbe : zeros (emLength emBits - salt.length - H.len - 2) ++ 0x01 :: salt = db
    at hdb hx hmasked
  have hdbl : db.length = emLength emBits - H.len - 1 := by rw [hdb]; omega
  have hdb' : clearTop (8 * emLength emBits - emBits)
      (xorBytes maskedDB (mgf1 G h (emLength emBits - H.len - 1))) = db := by
    rw [← hmasked, clearTop_xorBytes_clearTop, xorBytes_xorBytes (by omega), ← hdbe,
      clearTop_db hz]
  have htake : (maskedDB ++ h ++ [0xbc]).take (emLength emBits - H.len - 1) = maskedDB := by
    rw [List.append_assoc, List.take_left' hml]
  have hdrop : ((maskedDB ++ h ++ [0xbc]).drop (emLength emBits - H.len - 1)).take H.len = h := by
    rw [List.append_assoc, List.drop_left' hml, List.take_left' hh]
  have hidem : clearTop (8 * emLength emBits - emBits) maskedDB = maskedDB := by
    rw [← hmasked, clearTop_clearTop]
  have hc1 : ¬(mHash.length ≠ H.len ∨ (maskedDB ++ h ++ [0xbc]).length ≠ emLength emBits ∨
      emLength emBits < H.len + sLen.getD 0 + 2) := by
    rcases hs with rfl | rfl <;> simp [hm, hml, hh] <;> omega
  have hc2 : ¬((maskedDB ++ h ++ [0xbc]).getLast? ≠ some 0xbc) := by simp
  unfold verifyEncoding
  dsimp only
  rw [ite_eq_right hc1, ite_eq_right hc2, htake, hdrop, hidem, ite_eq_right (fun h => h rfl), hdb', ← hdbe,
    dropWhile_db]
  rw [List.append_assoc] at hhd
  rcases hs with rfl | rfl <;> simp [hhd]

/-- Only encodings verify: an encoding that verifies is that of the digest
with the salt it recovers, of the expected length. -/
theorem encode_of_verifyEncoding (hG : Valid G) {mHash em : List Byte} {emBits : Nat}
    {sLen : Option Nat} (hv : verifyEncoding H G mHash em emBits sLen = true) :
    ∃ salt, (sLen = none ∨ sLen = some salt.length) ∧
      encode H G mHash salt emBits = some em := by
  unfold verifyEncoding at hv
  dsimp only at hv
  split at hv
  · cases hv
  rename_i c1
  split at hv
  · cases hv
  rename_i c2
  split at hv
  · cases hv
  rename_i c3
  simp only [not_or, Decidable.not_not, Nat.not_lt] at c1 c2 c3
  obtain ⟨hm, hl, hlen⟩ := c1
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp c2
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  generalize hL : emLength emBits - H.len - 1 = L at *
  have hLy : L ≤ ys.length := by omega
  have hdl : (ys.drop L).length = H.len := by simp; omega
  have htake : (ys ++ [0xbc]).take L = ys.take L := List.take_append_of_le_length hLy
  have hdrop : ((ys ++ [0xbc]).drop L).take H.len = ys.drop L := by
    rw [List.drop_append_of_le_length hLy, List.take_left' hdl]
  rw [htake] at c3
  rw [htake, hdrop] at hv
  generalize hdb : clearTop (8 * emLength emBits - emBits)
    (xorBytes (ys.take L) (mgf1 G (ys.drop L) L)) = db at hv
  have hdbl : db.length = L := by
    rw [← hdb, clearTop_length, xorBytes_length, mgf1_length hG]; simp; omega
  split at hv
  · rename_i salt hd
    simp only [Bool.and_eq_true, beq_iff_eq] at hv
    obtain ⟨hs, hh⟩ := hv
    have hdbe := eq_db hd
    have hsl : salt.length + 1 ≤ L := by
      have := congrArg List.length hdbe
      simp only [db_length] at this; omega
    refine ⟨salt, ?_, ?_⟩
    · cases sLen with
      | none => exact .inl rfl
      | some n => exact .inr (by simpa using hs)
    · unfold encode
      dsimp only
      rw [ite_eq_right (by simp only [not_or, Decidable.not_not, Nat.not_lt]; omega), hh, hL]
      have hp : emLength emBits - salt.length - H.len - 2 = db.length - salt.length - 1 := by
        omega
      have hml : (ys.take L).length ≤ (mgf1 G (ys.drop L) L).length := by
        simp [mgf1_length hG]; omega
      rw [hp, ← hdbe, ← hdb, clearTop_xorBytes_clearTop, xorBytes_xorBytes hml, c3,
        List.take_append_drop]
  · cases hv

/-- `EMSA-PSS-VERIFY` accepts exactly the encodings of the digest with a salt
of the expected length. -/
theorem verifyEncoding_iff (hH : Valid H) (hG : Valid G) {mHash em : List Byte}
    {emBits : Nat} {sLen : Option Nat} :
    verifyEncoding H G mHash em emBits sLen = true ↔
      ∃ salt, (sLen = none ∨ sLen = some salt.length) ∧
        encode H G mHash salt emBits = some em :=
  ⟨encode_of_verifyEncoding hG, fun ⟨_, hs, he⟩ => verifyEncoding_encode hH hG he hs⟩

end VG.Proof.RsaPss
