module

public import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.Proof.RsaPss.Params

/-!
# RSASSA-PSS: signing and verification through the encoding

`sign` is the private-key operation on `zeros lo ++ encode …`, or a refusal
if the encoding fails (`sign_encode`), with `lo = k - emLen`; and `verify`,
for a modulus whose first octet is not zero, is whether the first `lo`
octets of RSAVP1's result (zeros if it fails) are zero and the rest a
consistent encoding (`verify_encode`).
-/

@[expose] public section

namespace VG.Proof.RsaPss

open Spec Spec.RsaPss
open Mgf1 (Hash)

variable (G : Hash)

theorem sign_encode {nB eB pB qB dPB dQB qInvB mHash salt : List Byte} {eb : Nat}
    (heb : bitLength (Rsa.os2ip nB) - 1 = eb) :
    sign G G nB eB pB qB dPB dQB qInvB mHash salt =
      match encode G G mHash salt eb with
      | some e => Rsa.privateChecked nB eB (zeros (nB.length - emLength eb) ++ e) pB qB dPB dQB qInvB
      | none => .invalid := by
  simp only [sign, encodeK, heb]
  cases encode G G mHash salt eb <;> rfl

/-- Whether the encoding fits: lengths alone. -/
theorem encode_isSome {mHash salt : List Byte} {eb : Nat} (hm : mHash.length = G.len) :
    (encode G G mHash salt eb).isSome = decide (G.len + salt.length + 2 ≤ emLength eb) := by
  unfold encode
  by_cases h : emLength eb < G.len + salt.length + 2
  · simp [hm, h]
  · simp [hm, h]; omega

/-- No encoding of zeros is consistent. -/
theorem verifyEncoding_zeros (mHash : List Byte) {n eb : Nat} (hn : 1 ≤ n) (sLen : Option Nat) :
    verifyEncoding G G mHash (zeros n) eb sLen = false := by
  have hl : (zeros n).getLast? ≠ some 0xbc := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [zeros, List.replicate_succ', List.getLast?_append]
  unfold verifyEncoding
  simp only [Bool.ite_false_left]
  simp
  intro _ _ _ h; exact absurd h hl

theorem verify_encode {nB eB mHash sB : List Byte} {sLen : Option Nat} {eb : Nat}
    (heb : bitLength (Rsa.os2ip nB) - 1 = eb) (hs : sB.length = nB.length) (hlo : 1 ≤ nB.length - (nB.length - emLength eb)) :
    verify G G nB eB mHash sB sLen =
      (((Rsa.publicOpChecked nB eB sB).getD (zeros nB.length)).take (nB.length - emLength eb) ==
          zeros (nB.length - emLength eb) &&
        verifyEncoding G G mHash (((Rsa.publicOpChecked nB eB sB).getD (zeros nB.length)).drop
          (nB.length - emLength eb)) eb sLen) := by
  simp only [verify, heb, hs, beq_self_eq_true, Bool.true_and]
  cases h : Rsa.publicOpChecked nB eB sB with
  | none =>
    have hz := verifyEncoding_zeros G mHash hlo sLen (eb := eb)
    simp only [Option.getD_none, zeros, List.drop_replicate] at hz ⊢
    rw [hz]
    simp
  | some x => simp

end VG.Proof.RsaPss
