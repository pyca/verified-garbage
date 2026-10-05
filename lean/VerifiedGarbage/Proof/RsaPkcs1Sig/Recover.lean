import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify

/-!
# RSASSA-PKCS1-v1_5 recovery by encoding

`recover_eq_recoverEnc`: the hash value a signature signs is the last
`hLen` octets of RSAVP1 of it, `EM`, if their encoding is `EM`, as OpenSSL's
`ossl_rsa_verify` with `rm` computes it: so an implementation can recover by
encoding those octets and comparing, with the encoding verification uses.
-/

namespace VG.Proof.RsaPkcs1Sig

open Spec.Rsa Spec.RsaPkcs1Sig

/-- The last `hLen` octets of `EM`, if their encoding is `EM`. -/
def recoverEnc (nB eB : List Byte) (h : Hash) (sig : List Byte) : Option (List Byte) :=
  if sig.length = nB.length then
    match publicOpChecked nB eB sig with
    | some em =>
      if encode h (em.drop (nB.length - h.len)) nB.length = some em then
        some (em.drop (nB.length - h.len))
      else none
    | none => none
  else none

/-- An encoding of `H` ends with `H`. -/
theorem drop_of_encode {h : Hash} {H em : List Byte} {k : Nat} (he : encode h H k = some em) :
    em.drop (k - h.len) = H := by
  have hk := encode_length he
  obtain ⟨hH, -, rfl⟩ := encode_eq_some_iff.1 he
  rw [show padded (k - (digestInfo h H).length - 3) (digestInfo h H) =
      ([0x00, 0x01] ++ List.replicate (k - (digestInfo h H).length - 3) 0xff ++ [0x00] ++ h.prefix) ++ H by
    simp [padded, digestInfo]] at hk ⊢
  rw [List.drop_left']
  rw [List.length_append] at hk
  omega

theorem recover_eq_recoverEnc (nB eB : List Byte) (h : Hash) (sig : List Byte) :
    recover nB eB h sig = recoverEnc nB eB h sig := by
  apply Option.ext
  intro H
  rw [recover_eq_some_iff, verify_iff_publicOpChecked, recoverEnc]
  by_cases hs : sig.length = nB.length
  · rw [ite_eq_left hs]
    simp only [hs, true_and]
    cases hp : publicOpChecked nB eB sig with
    | none => simp
    | some em =>
      simp only [Option.some.injEq]
      constructor
      · rintro ⟨em', he, rfl⟩
        rw [drop_of_encode he, ite_eq_left he]
      · intro hr
        by_cases he : encode h (em.drop (nB.length - h.len)) nB.length = some em
        · rw [ite_eq_left he, Option.some.injEq] at hr
          exact ⟨em, hr ▸ he, rfl⟩
        · rw [ite_eq_right he] at hr; cases hr
  · rw [ite_eq_right hs]
    simp [hs]

end VG.Proof.RsaPkcs1Sig
