import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Rsa.Checked

/-!
# RSASSA-PKCS1-v1_5 signing: what it releases verifies

* `verify_of_sign`: every signature `sign` releases is accepted by `verify`
  for the same hash value, whatever the key (`privateChecked` releases only
  a result whose `e`-th power is the encoding), so a faulted signing never
  releases a signature, valid or not.
* `sign_of_checkKey`: for every key `checkKey` (BoringSSL's
  `RSA_check_key`) accepts whose `p` and `q` are prime, and every hash value
  the modulus is long enough for, `sign` releases RSASP1 of the encoding,
  `EM^d mod n`: signing neither faults nor refuses the encoding.
* `sign_verify`: hence the round trip, for such a key.
-/

namespace VG.Proof.RsaPkcs1Sig

open Spec.Rsa Spec.RsaPkcs1Sig
open VG.Proof.Bignum (powMod_eq)

theorem valid_of_privateChecked_ok {nB eB xB pB qB dPB dQB qInvB y : List Byte}
    (h : privateChecked nB eB xB pB qB dPB dQB qInvB = .ok y) :
    modulusValid (os2ip nB) nB.length = true ∧ exponentValid (os2ip eB) = true := by
  unfold privateChecked at h
  by_cases hc : modulusValid (os2ip nB) nB.length = true ∧ exponentValid (os2ip eB) = true
  · exact hc
  · rw [ite_eq_right hc] at h; cases h

/-- Every signature `sign` releases is valid for the same hash value. -/
theorem verify_of_sign {nB eB pB qB dPB dQB qInvB : List Byte} {h : Hash} {H s : List Byte}
    (hs : sign nB eB pB qB dPB dQB qInvB h H = .ok s) : verify nB eB h H s = true := by
  unfold sign at hs
  cases he : encode h H nB.length with
  | none => rw [he] at hs; cases hs
  | some em =>
    rw [he] at hs
    obtain ⟨hl, hlt, hpow⟩ := Proof.Rsa.privateChecked_ok hs
    obtain ⟨hv, hev⟩ := valid_of_privateChecked_ok hs
    rw [verify_iff]
    exact ⟨hl, hv, hev, hlt, em, he, by rw [powMod_eq, hpow]⟩

theorem os2ip_zero_cons (l : List Byte) : os2ip (0 :: l) = os2ip l := by
  simp [os2ip]

/-- An encoding is below every valid modulus of its length: its first octet
is 0. -/
theorem encode_lt {h : Hash} {H em : List Byte} {nB : List Byte}
    (he : encode h H nB.length = some em) (hv : modulusValid (os2ip nB) nB.length = true) :
    os2ip em < os2ip nB := by
  obtain ⟨-, -, rfl⟩ := encode_eq_some_iff.1 he
  have hl' := encode_length he
  generalize hT : (0x01 :: (List.replicate (nB.length - (digestInfo h H).length - 3) 0xff ++
    0x00 :: digestInfo h H) : List Byte) = t
  have hcons : padded (nB.length - (digestInfo h H).length - 3) (digestInfo h H) = 0 :: t := by
    rw [← hT]; simp [padded]
  have he' : encode h H nB.length = some (0 :: t) := by rw [he, hcons]
  replace hl' := encode_length he'
  rw [hcons, os2ip_zero_cons]
  simp only [List.length_cons] at hl'
  have ht := os2ip_lt t
  rw [show t.length = nB.length - 1 by omega] at ht
  unfold modulusValid at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  exact Nat.lt_of_lt_of_le ht hv.2

/-- For a key `checkKey` accepts whose `p` and `q` are prime, signing a hash
value of `hLen` octets with a modulus of at least `tLen + 11` octets
releases RSASP1 of the encoding. -/
theorem sign_of_checkKey {nB eB dB pB qB dPB dQB qInvB : List Byte} {h : Hash} {H em : List Byte}
    (hk : checkKey nB eB dB pB qB dPB dQB qInvB = true) (hp : (os2ip pB).Prime)
    (hq : (os2ip qB).Prime) (he : encode h H nB.length = some em) :
    sign nB eB pB qB dPB dQB qInvB h H =
      .ok (i2osp (os2ip em ^ os2ip dB % os2ip nB) nB.length) := by
  have hv : modulusValid (os2ip nB) nB.length = true := by
    simp only [checkKey, keyValid, Bool.and_eq_true] at hk
    exact hk.1.1.1.1.1.1.1.1.1.1.1.1.1
  unfold sign
  rw [he]
  exact Proof.Rsa.privateChecked_of_checkKey hk hp hq (encode_lt he hv)

/-- Sign, then verify: for a key `checkKey` accepts whose `p` and `q` are
prime, every hash value that can be encoded (`hLen` octets, and `k` at
least `tLen + 11`) has a signature, and `verify` accepts it. -/
theorem sign_verify {nB eB dB pB qB dPB dQB qInvB : List Byte} {h : Hash} {H : List Byte}
    (hk : checkKey nB eB dB pB qB dPB dQB qInvB = true) (hp : (os2ip pB).Prime)
    (hq : (os2ip qB).Prime) (hH : H.length = h.len)
    (hlen : (digestInfo h H).length + 11 ≤ nB.length) :
    ∃ s, sign nB eB pB qB dPB dQB qInvB h H = .ok s ∧ verify nB eB h H s = true := by
  obtain ⟨em, he⟩ : ∃ em, encode h H nB.length = some em :=
    ⟨_, encode_eq_some_iff.2 ⟨hH, hlen, rfl⟩⟩
  have hs := sign_of_checkKey hk hp hq he
  exact ⟨_, hs, verify_of_sign hs⟩

end VG.Proof.RsaPkcs1Sig
