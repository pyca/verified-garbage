import VerifiedGarbage.Spec.RsaOaep
import VerifiedGarbage.Proof.RsaPss.Encoding

/-!
# EME-OAEP: decoding inverts encoding, and decodes nothing else

For hash functions whose digests are `hLen > 0` octets (`Mgf1.Valid`),
EME-OAEP decoding gives the message back from its encoding with any seed
(the round trip, `decode_encode`), and decodes an octet string to a message
only if it is the encoding of that message with some seed
(`encode_of_decode`): `decode_iff`.
-/

namespace VG.Proof.RsaOaep

open Spec Spec.RsaOaep

open Mgf1 (Hash xorBytes mgf1)
open Proof.Mgf1 (Valid xorBytes_length xorBytes_xorBytes mgf1_length)

variable {H G : Hash}

theorem dropWhile_ps (p : Nat) (m : List Byte) :
    (zeros p ++ 0x01 :: m).dropWhile (· == 0) = 0x01 :: m :=
  Proof.RsaPss.dropWhile_db p m

theorem eq_ps {ps m : List Byte} (h : ps.dropWhile (· == 0) = 0x01 :: m) :
    ps = zeros (ps.length - m.length - 1) ++ 0x01 :: m :=
  Proof.RsaPss.eq_db h

theorem ps_length (p : Nat) (m : List Byte) : (zeros p ++ 0x01 :: m).length = p + m.length + 1 :=
  Proof.RsaPss.db_length p m

/-- Decoding gives the message back from its encoding. -/
theorem decode_encode (hH : Valid H) (hG : Valid G) {label m seed em : List Byte} {k : Nat}
    (he : encode H G label m seed k = some em) : decode H G label em = some m := by
  unfold encode at he
  dsimp only at he
  split at he
  · cases he
  rename_i hc
  simp only [not_or, Decidable.not_not, Nat.not_lt] at hc
  obtain ⟨hs, hk⟩ := hc
  cases he
  have hl := hH.2 label
  generalize hdbe : H.hash label ++ zeros (k - m.length - 2 * H.len - 2) ++ 0x01 :: m = db
  have hdbl : db.length = k - H.len - 1 := by
    rw [← hdbe, List.append_assoc, List.length_append, ps_length, hl]; omega
  have hmask := mgf1_length hG seed (k - H.len - 1)
  generalize hmdb : xorBytes db (mgf1 G seed (k - H.len - 1)) = maskedDB
  have hmdbl : maskedDB.length = k - H.len - 1 := by rw [← hmdb, xorBytes_length]; omega
  have hsm := mgf1_length hG maskedDB H.len
  generalize hms : xorBytes seed (mgf1 G maskedDB H.len) = maskedSeed
  have hmsl : maskedSeed.length = H.len := by rw [← hms, xorBytes_length]; omega
  have hseed : xorBytes maskedSeed (mgf1 G maskedDB H.len) = seed := by
    rw [← hms, xorBytes_xorBytes (by omega)]
  have hdb : xorBytes maskedDB (mgf1 G seed (k - H.len - 1)) = db := by
    rw [← hmdb, xorBytes_xorBytes (by omega)]
  have hlen : (0x00 :: maskedSeed ++ maskedDB).length = k := by simp; omega
  have hms' : ((0x00 :: maskedSeed ++ maskedDB).drop 1).take H.len = maskedSeed := by
    simp [List.take_left' hmsl]
  have hmdb' : (0x00 :: maskedSeed ++ maskedDB).drop (H.len + 1) = maskedDB := by
    simp [List.drop_left' hmsl]
  have hdrop : db.drop H.len = zeros (k - m.length - 2 * H.len - 2) ++ 0x01 :: m := by
    rw [← hdbe, List.append_assoc, List.drop_left' hl]
  have htake : db.take H.len = H.hash label := by
    rw [← hdbe, List.append_assoc, List.take_left' hl]
  unfold decode
  dsimp only
  rw [hlen, ite_eq_right (by omega), hms', hmdb', hseed, hdb, hdrop, dropWhile_ps, htake]
  simp

/-- Decoding gives a message only from an encoding of it. -/
theorem encode_of_decode (hG : Valid G) {label m em : List Byte}
    (hd : decode H G label em = some m) :
    ∃ seed, encode H G label m seed em.length = some em := by
  unfold decode at hd
  dsimp only at hd
  split at hd
  · cases hd
  rename_i hk
  simp only [Nat.not_lt] at hk
  generalize hk' : em.length = k at hk ⊢ hd
  generalize hms : (em.drop 1).take H.len = maskedSeed at hd
  generalize hmdb : em.drop (H.len + 1) = maskedDB at hd
  have hmsl : maskedSeed.length = H.len := by rw [← hms]; simp; omega
  have hmdbl : maskedDB.length = k - H.len - 1 := by rw [← hmdb]; simp; omega
  generalize hseed : xorBytes maskedSeed (mgf1 G maskedDB H.len) = seed at hd
  have hseedl : seed.length = H.len := by
    rw [← hseed, xorBytes_length, mgf1_length hG]; omega
  generalize hdb : xorBytes maskedDB (mgf1 G seed (k - H.len - 1)) = db at hd
  have hdbl : db.length = k - H.len - 1 := by
    rw [← hdb, xorBytes_length, mgf1_length hG]; omega
  split at hd
  · rename_i m' hps
    split at hd
    · rename_i hc
      cases hd
      obtain ⟨hy, hl⟩ := hc
      have hpse := eq_ps hps
      have hp : (db.drop H.len).length - m.length - 1 = k - m.length - 2 * H.len - 2 := by
        have hpl := congrArg List.length hpse
        rw [ps_length] at hpl
        simp only [List.length_drop] at hpl ⊢
        omega
      rw [hp] at hpse
      have hdbe : db = H.hash label ++ zeros (k - m.length - 2 * H.len - 2) ++ 0x01 :: m := by
        rw [← List.take_append_drop H.len db, hl, hpse, List.append_assoc]
      have hem : em = 0x00 :: maskedSeed ++ maskedDB := by
        rw [← hms, ← hmdb]
        cases em with
        | nil => simp at hy
        | cons y ys =>
          simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at hy
          subst hy
          simp [List.take_append_drop]
      have hml : 2 * H.len + 2 + m.length ≤ k := by
        have := congrArg List.length hpse
        rw [ps_length, List.length_drop] at this
        omega
      refine ⟨seed, ?_⟩
      unfold encode
      dsimp only
      rw [ite_eq_right (by omega), ← hdbe,
        ← hdb, xorBytes_xorBytes (by rw [mgf1_length hG]; omega), ← hseed,
        xorBytes_xorBytes (by rw [mgf1_length hG]; omega), hem]
    · cases hd
  · cases hd

/-- EME-OAEP decoding gives `m` exactly from the encodings of `m`. -/
theorem decode_iff (hH : Valid H) (hG : Valid G) {label m em : List Byte} :
    decode H G label em = some m ↔ ∃ seed, encode H G label m seed em.length = some em :=
  ⟨encode_of_decode hG, fun ⟨_, he⟩ => decode_encode hH hG he⟩

end VG.Proof.RsaOaep
