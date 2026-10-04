import VerifiedGarbage.Proof.RsaPss.Encoding

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
open Rsa (publicOp)

variable {H G : Hash}

theorem verify_iff (hH : Valid H) (hG : Valid G) {nB eB mHash sB : List Byte}
    {sLen : Option Nat} :
    verify H G nB eB mHash sB sLen = true ↔
      sB.length = nB.length ∧ ∃ salt em, (sLen = none ∨ sLen = some salt.length) ∧
        encodeK H G nB mHash salt = some em ∧ publicOp nB eB sB = some em := by
  unfold verify encodeK
  dsimp only
  generalize nB.length - emLength (bitLength (Rsa.os2ip nB) - 1) = d
  simp only [Bool.and_eq_true, beq_iff_eq, and_congr_right_iff]
  intro _
  cases publicOp nB eB sB with
  | none => simp
  | some x =>
    simp only [Bool.and_eq_true, beq_iff_eq, verifyEncoding_iff hH hG]
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
