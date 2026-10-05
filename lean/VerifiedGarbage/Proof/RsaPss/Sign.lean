import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.Rsa.Checked

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPss.Encoding`. -/
section

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
  cases a <;> cases b <;> simp [clearTop, xorBytes, VG.Proof.RsaPss.byte_and_xor_and]

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
  have hdb := VG.Proof.RsaPss.db_length (emLength emBits - salt.length - H.len - 2) salt
  have hx := xorBytes_length (zeros (emLength emBits - salt.length - H.len - 2) ++ 0x01 :: salt)
    (mgf1 G (H.hash (zeros 8 ++ mHash ++ salt)) (emLength emBits - H.len - 1))
  generalize hmasked : clearTop (8 * emLength emBits - emBits) (xorBytes
    (zeros (emLength emBits - salt.length - H.len - 2) ++ 0x01 :: salt)
    (mgf1 G (H.hash (zeros 8 ++ mHash ++ salt)) (emLength emBits - H.len - 1))) = maskedDB
  have hml : maskedDB.length = emLength emBits - H.len - 1 := by
    rw [← hmasked, VG.Proof.RsaPss.clearTop_length, hx, hdb, hmask]; omega
  generalize hhd : H.hash (zeros 8 ++ mHash ++ salt) = h at hh hmask hx hmasked ⊢
  generalize hdbe : zeros (emLength emBits - salt.length - H.len - 2) ++ 0x01 :: salt = db
    at hdb hx hmasked
  have hdbl : db.length = emLength emBits - H.len - 1 := by rw [hdb]; omega
  have hdb' : clearTop (8 * emLength emBits - emBits)
      (xorBytes maskedDB (mgf1 G h (emLength emBits - H.len - 1))) = db := by
    rw [← hmasked, VG.Proof.RsaPss.clearTop_xorBytes_clearTop, xorBytes_xorBytes (by omega), ← hdbe,
      VG.Proof.RsaPss.clearTop_db hz]
  have htake : (maskedDB ++ h ++ [0xbc]).take (emLength emBits - H.len - 1) = maskedDB := by
    rw [List.append_assoc, List.take_left' hml]
  have hdrop : ((maskedDB ++ h ++ [0xbc]).drop (emLength emBits - H.len - 1)).take H.len = h := by
    rw [List.append_assoc, List.drop_left' hml, List.take_left' hh]
  have hidem : clearTop (8 * emLength emBits - emBits) maskedDB = maskedDB := by
    rw [← hmasked, VG.Proof.RsaPss.clearTop_clearTop]
  have hc1 : ¬(mHash.length ≠ H.len ∨ (maskedDB ++ h ++ [0xbc]).length ≠ emLength emBits ∨
      emLength emBits < H.len + sLen.getD 0 + 2) := by
    rcases hs with rfl | rfl <;> simp [hm, hml, hh] <;> omega
  have hc2 : ¬((maskedDB ++ h ++ [0xbc]).getLast? ≠ some 0xbc) := by simp
  unfold verifyEncoding
  dsimp only
  rw [ite_eq_right hc1, ite_eq_right hc2, htake, hdrop, hidem, ite_eq_right (fun h => h rfl), hdb', ← hdbe,
    VG.Proof.RsaPss.dropWhile_db]
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
    rw [← hdb, VG.Proof.RsaPss.clearTop_length, xorBytes_length, mgf1_length hG]; simp; omega
  split at hv
  · rename_i salt hd
    simp only [Bool.and_eq_true, beq_iff_eq] at hv
    obtain ⟨hs, hh⟩ := hv
    have hdbe := VG.Proof.RsaPss.eq_db hd
    have hsl : salt.length + 1 ≤ L := by
      have := congrArg List.length hdbe
      simp only [VG.Proof.RsaPss.db_length] at this; omega
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
        simp [mgf1_length hG]
      rw [hp, ← hdbe, ← hdb, VG.Proof.RsaPss.clearTop_xorBytes_clearTop, xorBytes_xorBytes hml, c3,
        List.take_append_drop]
  · cases hv

/-- `EMSA-PSS-VERIFY` accepts exactly the encodings of the digest with a salt
of the expected length. -/
theorem verifyEncoding_iff (hH : Valid H) (hG : Valid G) {mHash em : List Byte}
    {emBits : Nat} {sLen : Option Nat} :
    verifyEncoding H G mHash em emBits sLen = true ↔
      ∃ salt, (sLen = none ∨ sLen = some salt.length) ∧
        encode H G mHash salt emBits = some em :=
  ⟨VG.Proof.RsaPss.encode_of_verifyEncoding hG, fun ⟨_, hs, he⟩ => VG.Proof.RsaPss.verifyEncoding_encode hH hG he hs⟩

end VG.Proof.RsaPss

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPss.Verify`. -/
section

/-!
# RSASSA-PSS: verification accepts exactly the signatures of encodings

`RSASSA-PSS-VERIFY` accepts a signature exactly when it is `k` octets and
RSAVP1 takes it to the encoding (as `k` octets, `encodeK`) of the digest with
some salt of the expected length (`verify_iff`). So a signature that RSASP1
gives for such an encoding, which the checked private-key operation releases
only if RSAVP1 takes it back to that encoding, verifies.
-/

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss

open Mgf1 (Hash)
open Proof.Mgf1 (Valid)
open Rsa (publicOpChecked)

variable {H G : Hash}

theorem verify_iff (hH : Valid H) (hG : Valid G) {nB eB mHash sB : List Byte}
    {sLen : Option Nat} :
    verify H G nB eB mHash sB sLen = true ↔
      sB.length = nB.length ∧ ∃ salt em, (sLen = none ∨ sLen = some salt.length) ∧
        encodeK H G nB mHash salt = some em ∧ publicOpChecked nB eB sB = some em := by
  unfold verify encodeK
  dsimp only
  generalize nB.length - emLength (bitLength (Rsa.os2ip nB) - 1) = d
  simp only [Bool.and_eq_true, beq_iff_eq, and_congr_right_iff]
  intro _
  cases publicOpChecked nB eB sB with
  | none => simp
  | some x =>
    simp only [Bool.and_eq_true, beq_iff_eq, VG.Proof.RsaPss.verifyEncoding_iff hH hG]
    constructor
    · rintro ⟨hz, salt, hs, he⟩
      refine ⟨salt, x, hs, ?_, rfl⟩
      rw [he, Option.map_some, ← hz, List.take_append_drop]
    · rintro ⟨salt, em, hs, he, hx⟩
      cases hx
      cases hc : encode H G mHash salt (bitLength (Rsa.os2ip nB) - 1) with
      | none => simp [hc] at he
      | some em' =>
        simp only [hc, Option.map_some, Option.some.injEq] at he
        subst he
        have hl : (zeros d).length = d := List.length_replicate
        exact ⟨List.take_left' hl, salt, hs, by rw [List.drop_left' hl, hc]⟩

end VG.Proof.RsaPss

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPss.Sign`. -/
section

/-!
# RSASSA-PSS: every signature verifies

A signature that `sign` releases verifies, with its salt's length or with
any (`verify_sign`): `privateChecked` releases a signature only if RSAVP1
takes it back to the encoding (`Proof.Rsa.privateChecked_ok`), and
verification accepts every encoding (`verify_iff`). This needs nothing of
the key: for a key `checkKey` accepts with prime factors, `sign` never
faults (`Proof.Rsa.privateChecked_ne_fault`).
-/

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss

open Mgf1 (Hash)
open Proof.Mgf1 (Valid)
open Rsa (os2ip i2osp publicOp publicOpChecked privateChecked modulusValid exponentValid)
open Proof.Rsa (os2ip_snoc i2osp_succ i2osp_length lt_of_os2ip privateChecked_ok)

variable {H G : Hash}

/-- OS2IP then I2OSP to the same length gives the octets back. -/
theorem i2osp_os2ip (bs : List Byte) : i2osp (os2ip bs) bs.length = bs := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    rw [List.length_append, List.length_singleton, i2osp_succ, os2ip_snoc]
    have hb := b.isLt
    have hd : (256 * os2ip l + b.toNat) / 256 = os2ip l := by omega
    rw [hd, ih]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega

/-- What `privateChecked` releases is for a valid modulus and exponent. -/
theorem privateChecked_valid {nB eB xB pB qB dPB dQB qInvB y : List Byte}
    (h : privateChecked nB eB xB pB qB dPB dQB qInvB = .ok y) :
    modulusValid (os2ip nB) nB.length ∧ exponentValid (os2ip eB) := by
  unfold privateChecked at h
  dsimp only at h
  split at h
  · rename_i hv; exact hv
  · cases h

/-- An encoding is `emLen` octets. -/
theorem encode_length (hH : Valid H) (hG : Valid G) {mHash salt em : List Byte} {emBits : Nat}
    (he : encode H G mHash salt emBits = some em) : em.length = emLength emBits := by
  have hv := VG.Proof.RsaPss.verifyEncoding_encode hH hG he (.inl rfl)
  unfold verifyEncoding at hv
  dsimp only at hv
  split at hv
  · cases hv
  · rename_i hc
    simp only [not_or, Decidable.not_not] at hc
    exact hc.2.1

/-- The encoding `encodeK` gives for a valid modulus is `k` octets. -/
theorem encodeK_length (hH : Valid H) (hG : Valid G) {nB mHash salt em : List Byte}
    (hn : modulusValid (os2ip nB) nB.length)
    (he : encodeK H G nB mHash salt = some em) : em.length = nB.length := by
  unfold encodeK at he
  cases hc : encode H G mHash salt (bitLength (os2ip nB) - 1) with
  | none => simp [hc] at he
  | some x =>
    simp only [hc, Option.map_some, Option.some.injEq] at he
    subst he
    have hx := VG.Proof.RsaPss.encode_length hH hG hc
    have hlt := lt_of_os2ip nB
    have hpos : 0 < os2ip nB := by
      simp only [modulusValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hn; omega
    have hlog : Nat.log2 (os2ip nB) < 8 * nB.length := by
      rw [Nat.log2_lt (by omega)]
      rw [show 256 ^ nB.length = 2 ^ (8 * nB.length) by rw [Nat.pow_mul]] at hlt
      exact hlt
    simp only [List.length_append, zeros, List.length_replicate, hx, emLength, bitLength]
    omega

/-- Every signature `sign` releases verifies, with its salt's length or with
any. -/
theorem verify_sign (hH : Valid H) (hG : Valid G)
    {nB eB pB qB dPB dQB qInvB mHash salt sB : List Byte} {sLen : Option Nat}
    (hs : sign H G nB eB pB qB dPB dQB qInvB mHash salt = .ok sB)
    (hl : sLen = none ∨ sLen = some salt.length) :
    verify H G nB eB mHash sB sLen = true := by
  unfold sign at hs
  cases he : encodeK H G nB mHash salt with
  | none => simp [he] at hs
  | some em =>
    simp only [he] at hs
    obtain ⟨hlen, hlt, hpow⟩ := privateChecked_ok hs
    obtain ⟨hn, hev⟩ := VG.Proof.RsaPss.privateChecked_valid hs
    have hem := VG.Proof.RsaPss.encodeK_length hH hG hn he
    have hpub : publicOpChecked nB eB sB = some em := by
      simp only [publicOpChecked, hev, ite_true, publicOp, hn, Rsa.encrypt, hlt,
        Option.map_some, Proof.Bignum.powMod_eq, hpow]
      rw [← hem, VG.Proof.RsaPss.i2osp_os2ip]
    exact (VG.Proof.RsaPss.verify_iff hH hG).mpr ⟨hlen, salt, em, hl, he, hpub⟩

end VG.Proof.RsaPss

end
