import VerifiedGarbage.Spec.RsaOaep
import VerifiedGarbage.Proof.RsaPss.Sign
import VerifiedGarbage.Spec.RsaOaep.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.RsaOaep.Encoding`. -/
section

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
    rw [← hdbe, List.append_assoc, List.length_append, VG.Proof.RsaOaep.ps_length, hl]; omega
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
  rw [hlen, ite_eq_right (by omega), hms', hmdb', hseed, hdb, hdrop, VG.Proof.RsaOaep.dropWhile_ps, htake]
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
      have hpse := VG.Proof.RsaOaep.eq_ps hps
      have hp : (db.drop H.len).length - m.length - 1 = k - m.length - 2 * H.len - 2 := by
        have hpl := congrArg List.length hpse
        rw [VG.Proof.RsaOaep.ps_length] at hpl
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
        rw [VG.Proof.RsaOaep.ps_length, List.length_drop] at this
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
  ⟨VG.Proof.RsaOaep.encode_of_decode hG, fun ⟨_, he⟩ => VG.Proof.RsaOaep.decode_encode hH hG he⟩

end VG.Proof.RsaOaep

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaOaep.Decrypt`. -/
section

/-!
# RSAES-OAEP decryption: one error, and the round trip

* `decrypt_ok_iff`: decryption gives `m` exactly when the checked RSADP
  releases an encoding of `m` (with some seed).
* `decrypt_eq_invalid_of_decode`: every decoding failure is the same
  outcome, `invalid`, as a refused key or ciphertext.
* `decrypt_eq_of_failed`, `writtenDecrypt_eq`: the error carries no
  information beyond one bit. Every failure but the internal fault is the
  same outcome, and what the contract lets an implementation write for it
  (the return value, the `n_len` octets at `out` and the length) is the same
  whatever the key, the label and the ciphertext; constant time (the
  contract's `leak` is the public key) keeps timing from telling more.
* `decrypt_ne_fault`, `decrypt_encrypt`: for a key `checkKey` accepts with
  prime factors, decryption never faults, and decrypts every encryption.
-/

namespace VG.Proof.RsaOaep

open Spec Spec.RsaOaep

open Mgf1 (Hash)
open Proof.Mgf1 (Valid)
open Rsa (os2ip i2osp publicOp publicOpChecked privateChecked modulusValid exponentValid
  checkKey keyValid Outcome)
open Proof.Rsa (os2ip_i2osp i2osp_length lt_of_os2ip privateChecked_of_checkKey
  privateChecked_ne_fault pow_modEq_of_modEq)
open Proof.RsaPss (i2osp_os2ip)

variable {H G : Hash}

theorem decrypt_ok_iff {nB eB pB qB dPB dQB qInvB label cB m : List Byte} (hG : Valid G)
    (hH : Valid H) :
    decrypt H G nB eB pB qB dPB dQB qInvB label cB = .ok m ↔
      cB.length = nB.length ∧ ∃ em seed, privateChecked nB eB cB pB qB dPB dQB qInvB = .ok em ∧
        encode H G label m seed em.length = some em := by
  unfold decrypt
  split
  · rename_i hl; simp [hl]
  · rename_i hl
    simp only [Decidable.not_not] at hl
    simp only [hl, true_and]
    cases hp : privateChecked nB eB cB pB qB dPB dQB qInvB with
    | ok em =>
      simp only [Outcome.ok.injEq]
      constructor
      · intro h
        cases hd : decode H G label em with
        | none => simp [hd] at h
        | some m' =>
          simp only [hd, Outcome.ok.injEq] at h
          subst h
          obtain ⟨seed, he⟩ := (VG.Proof.RsaOaep.decode_iff hH hG).mp hd
          exact ⟨em, seed, rfl, he⟩
      · rintro ⟨_, seed, rfl, he⟩
        simp [(VG.Proof.RsaOaep.decode_iff hH hG).mpr ⟨seed, he⟩]
    | invalid => simp
    | fault => simp

/-- Every decoding failure is `invalid`, the outcome of every other failure
but the internal fault. -/
theorem decrypt_eq_invalid_of_decode {nB eB pB qB dPB dQB qInvB label cB em : List Byte}
    (hp : privateChecked nB eB cB pB qB dPB dQB qInvB = .ok em) (hd : decode H G label em = none) :
    decrypt H G nB eB pB qB dPB dQB qInvB label cB = .invalid := by
  unfold decrypt
  split
  · rfl
  · rw [hp]; simp only [hd]

/-- Decryption fails with one error: every outcome but a message and the
internal fault is `invalid`. -/
theorem decrypt_eq_of_failed {nB eB pB qB dPB dQB qInvB label cB : List Byte}
    (hm : ∀ m, decrypt H G nB eB pB qB dPB dQB qInvB label cB ≠ .ok m)
    (hf : decrypt H G nB eB pB qB dPB dQB qInvB label cB ≠ .fault) :
    decrypt H G nB eB pB qB dPB dQB qInvB label cB = .invalid := by
  cases h : decrypt H G nB eB pB qB dPB dQB qInvB label cB with
  | ok m => exact absurd h (hm m)
  | invalid => rfl
  | fault => exact absurd h hf

/-- What the contract lets decryption write for a failure is the same
whatever the inputs: the return value, the octets at `out` and the length. -/
theorem writtenDecrypt_eq {m₁ m₂ : Mem} {out₁ out₂ len₁ len₂ : Addr} {nLen : Nat}
    {r₁ r₂ : BitVec 32} (h₁ : writtenDecrypt m₁ out₁ len₁ nLen r₁ .invalid)
    (h₂ : writtenDecrypt m₂ out₂ len₂ nLen r₂ .invalid) :
    r₁ = r₂ ∧ Rsa.bytesAt m₁ out₁ nLen = Rsa.bytesAt m₂ out₂ nLen ∧
      m₁.readW len₁ 64 = m₂.readW len₂ 64 := by
  obtain ⟨hr₁, hb₁, hl₁⟩ := h₁
  obtain ⟨hr₂, hb₂, hl₂⟩ := h₂
  exact ⟨hr₁.trans hr₂.symm, hb₁.trans hb₂.symm, hl₁.trans hl₂.symm⟩

/-- For a key `checkKey` accepts with prime factors, decryption never
faults. -/
theorem decrypt_ne_fault {nB eB dB pB qB dPB dQB qInvB label cB : List Byte}
    (hk : checkKey nB eB dB pB qB dPB dQB qInvB = true) (hp : (os2ip pB).Prime)
    (hq : (os2ip qB).Prime) : decrypt H G nB eB pB qB dPB dQB qInvB label cB ≠ .fault := by
  have := privateChecked_ne_fault cB hk hp hq
  unfold decrypt
  split
  · nofun
  · cases h : privateChecked nB eB cB pB qB dPB dQB qInvB with
    | ok em => cases hd : decode H G label em <;> simp [hd]
    | invalid => nofun
    | fault => exact absurd h this

/-- For a key `keyValid` accepts with prime factors, `x^(d e) ≡ x (mod n)`. -/
theorem pow_de_mod {k n e d p q dP dQ qInv : Nat} (hk : keyValid k n e d p q dP dQ qInv = true)
    (hp : p.Prime) (hq : q.Prime) (x : Nat) : x ^ (d * e) % n = x % n := by
  simp only [keyValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at hk
  obtain ⟨-, -, -, -, -, hpq, hdep, hdeq, -, -, -, -, hqip, hqi⟩ := hk
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hp1 : 1 < p - 1 := by
    rcases (show p - 1 = 1 ∨ 1 < p - 1 by omega) with h | h
    · rw [h, Nat.mod_one] at hdep; omega
    · exact h
  have hq1 : 1 < q - 1 := by
    rcases (show q - 1 = 1 ∨ 1 < q - 1 by omega) with h | h
    · rw [h, Nat.mod_one] at hdeq; omega
    · exact h
  have pos : ∀ {x y m : Nat}, x * y % m = 1 → 0 < x ∧ 0 < y := by
    intro x y m h
    constructor <;> refine Nat.pos_of_ne_zero fun h0 => ?_ <;> simp [h0] at h
  have hcop : p.Coprime q :=
    Nat.coprime_comm.1 (Nat.coprime_of_mul_modEq_one qInv (by
      show q * qInv % p = 1 % p; rw [hqi, Nat.mod_eq_of_lt (by omega)]))
  have hp' : x ^ (d * e) ≡ x ^ 1 [MOD p] :=
    pow_modEq_of_modEq hp (Nat.mul_pos (pos hdep).1 (pos hdep).2) Nat.one_pos
      (by show d * e % (p - 1) = 1 % (p - 1); rw [hdep, Nat.mod_eq_of_lt hp1]) x
  have hq' : x ^ (d * e) ≡ x ^ 1 [MOD q] :=
    pow_modEq_of_modEq hq (Nat.mul_pos (pos hdeq).1 (pos hdeq).2) Nat.one_pos
      (by show d * e % (q - 1) = 1 % (q - 1); rw [hdeq, Nat.mod_eq_of_lt hq1]) x
  have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hp', hq'⟩
  rw [hpq, Nat.pow_one] at this
  exact this

/-- An encoding is `k` octets. -/
theorem encode_length {label m seed em : List Byte} {k : Nat} (hH : Valid H) (hG : Valid G)
    (he : encode H G label m seed k = some em) : em.length = k := by
  unfold encode at he
  dsimp only at he
  split at he
  · cases he
  rename_i hc
  simp only [not_or, Decidable.not_not, Nat.not_lt] at hc
  cases he
  simp only [List.length_cons, List.length_append, Proof.Mgf1.xorBytes_length,
    Proof.Mgf1.mgf1_length hG, hH.2, zeros, List.length_replicate]
  omega

/-- The round trip: for a key `checkKey` accepts with prime factors,
decryption with the label gives back every message encrypted with it. -/
theorem decrypt_encrypt (hH : Valid H) (hG : Valid G)
    {nB eB dB pB qB dPB dQB qInvB label m seed cB : List Byte}
    (hk : checkKey nB eB dB pB qB dPB dQB qInvB = true) (hp : (os2ip pB).Prime)
    (hq : (os2ip qB).Prime) (hc : encrypt H G nB eB label m seed = some cB) :
    decrypt H G nB eB pB qB dPB dQB qInvB label cB = .ok m := by
  unfold encrypt at hc
  cases he : encode H G label m seed nB.length with
  | none => simp [he] at hc
  | some em =>
    simp only [he, Option.bind_some, publicOpChecked] at hc
    split at hc
    · rename_i hev
      unfold publicOp at hc
      dsimp only at hc
      split at hc
      · rename_i hn
        simp only [Rsa.encrypt] at hc
        split at hc
        · rename_i hlt
          simp only [Option.map_some, Option.some.injEq, Proof.Bignum.powMod_eq] at hc
          subst hc
          have hn' : os2ip nB < 256 ^ nB.length := lt_of_os2ip nB
          have hcl : (i2osp (os2ip em ^ os2ip eB % os2ip nB) nB.length).length = nB.length :=
            i2osp_length _ _
          have hcv : os2ip (i2osp (os2ip em ^ os2ip eB % os2ip nB) nB.length) =
              os2ip em ^ os2ip eB % os2ip nB := by
            rw [os2ip_i2osp, Nat.mod_eq_of_lt (by
              have := Nat.mod_lt (os2ip em ^ os2ip eB) (show 0 < os2ip nB by omega); omega)]
          have hpc := privateChecked_of_checkKey (xB := i2osp (os2ip em ^ os2ip eB % os2ip nB)
            nB.length) hk hp hq (by rw [hcv]; exact Nat.mod_lt _ (by omega))
          rw [hcv, ← Nat.pow_mod, ← Nat.pow_mul] at hpc
          have hkv := hk
          simp only [checkKey] at hkv
          rw [Nat.mul_comm, VG.Proof.RsaOaep.pow_de_mod hkv hp hq, Nat.mod_eq_of_lt hlt] at hpc
          have hel := VG.Proof.RsaOaep.encode_length hH hG he
          have hid : i2osp (os2ip em) nB.length = em := by rw [← hel]; exact i2osp_os2ip em
          rw [hid] at hpc
          unfold decrypt
          rw [ite_eq_right (by rw [hcl]; exact fun h => h rfl), hpc]
          simp only [VG.Proof.RsaOaep.decode_encode hH hG he]
        · cases hc
      · cases hc
    · cases hc

end VG.Proof.RsaOaep

end
