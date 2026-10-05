import VerifiedGarbage.Proof.RsaPss.EncBytes

/-!
# RSASSA-PSS signing, by cases

`sign` refuses a modulus whose first octet is zero (`sign_zero`) and a salt
that does not fit (`sign_long`), and is otherwise the checked private-key
operation on the encoding, byte by byte (`sign_eq`).
-/

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss
open Mgf1 (Hash)
open Proof.Mgf1 (Valid)

variable (G : Hash)

theorem os2ip_zero_cons (rest : List Byte) : Rsa.os2ip (0 :: rest) = Rsa.os2ip rest := by
  rw [os2ip_cons']; simp

theorem privateChecked_zero (rest eB xB pB qB dPB dQB qInvB : List Byte) :
    Rsa.privateChecked (0 :: rest) eB xB pB qB dPB dQB qInvB = .invalid := by
  have := os2ip_lt' rest
  simp only [Rsa.privateChecked, Rsa.modulusValid, os2ip_zero_cons, List.length_cons, Nat.add_sub_cancel]
  rw [ifn]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  intro ⟨⟨_, h⟩, _⟩; omega

theorem sign_zero (rest eB pB qB dPB dQB qInvB mHash salt : List Byte) :
    sign G G (0 :: rest) eB pB qB dPB dQB qInvB mHash salt = .invalid := by
  unfold sign
  split
  · exact privateChecked_zero ..
  · rfl

theorem sign_long {nB : List Byte} (eB pB qB dPB dQB qInvB mHash salt : List Byte)
    (h : emLength (bitLength (Rsa.os2ip nB) - 1) < G.len + salt.length + 2) :
    sign G G nB eB pB qB dPB dQB qInvB mHash salt = .invalid := by
  simp only [sign, encodeK, encode]
  rw [ifp (Or.inr h)]
  rfl

theorem sign_eq (hG : Valid G) {n₀ : Byte} {rest eB pB qB dPB dQB qInvB mHash salt : List Byte} (h0 : n₀ ≠ 0)
    (hm : mHash.length = G.len) {emBits emLen lo db : Nat}
    (hb : bitLength (Rsa.os2ip (n₀ :: rest)) - 1 = emBits) (he : emLength emBits = emLen)
    (hlo : (n₀ :: rest).length - emLen = lo) (hdb : emLen - G.len - 1 = db)
    (hfit : G.len + salt.length + 2 ≤ emLen) :
    sign G G (n₀ :: rest) eB pB qB dPB dQB qInvB mHash salt =
      Rsa.privateChecked (n₀ :: rest) eB ((List.range (n₀ :: rest).length).map
        (emT lo db salt.length salt (G.hash (zeros 8 ++ mHash ++ salt))
          (Mgf1.mgf1 G (G.hash (zeros 8 ++ mHash ++ salt)) db) ((0xFF : Byte) >>> (8 * emLen - emBits))))
        pB qB dPB dQB qInvB := by
  simp only [sign, encodeK_eq G hG h0 hm hb he hlo hdb hfit]

end VG.Proof.RsaPss
