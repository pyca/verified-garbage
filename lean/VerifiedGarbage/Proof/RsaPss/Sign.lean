import VerifiedGarbage.Proof.RsaPss.Verify
import VerifiedGarbage.Proof.Rsa.Checked

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
  have hv := verifyEncoding_encode hH hG he (.inl rfl)
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
    have hx := encode_length hH hG hc
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
    obtain ⟨hn, hev⟩ := privateChecked_valid hs
    have hem := encodeK_length hH hG hn he
    have hpub : publicOpChecked nB eB sB = some em := by
      simp only [publicOpChecked, hev, ite_true, publicOp, hn, Rsa.encrypt, hlt,
        Option.map_some, Proof.Bignum.powMod_eq, hpow]
      rw [← hem, i2osp_os2ip]
    exact (verify_iff hH hG).mpr ⟨hlen, salt, em, hl, he, hpub⟩

end VG.Proof.RsaPss
