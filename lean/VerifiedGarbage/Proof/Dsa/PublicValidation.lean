module

public import VerifiedGarbage.Spec.Dsa.Prevalidated

/-! # Public-key validation is necessary for the existing verification result -/

@[expose] public section

namespace VG.Proof.Dsa

open VG.Spec.Dsa

/-- Factoring validation out cannot turn an invalid public key into an
accepted signature: the original verifier already implies this predicate. -/
theorem verifyBytes_validation (pLen qLen : Nat) (key signature digest : List VG.Byte) :
    verifyBytes pLen qLen key signature digest =
      (validatePublicKeyBytes pLen qLen key && verifyBytes pLen qLen key signature digest) := by
  by_cases hw : lengthsValid pLen qLen
  · by_cases hl : key.length = 3*pLen+qLen
    · by_cases hs : signature.length = 2*qLen
      · by_cases hp : parametersValid (publicKeyBytes pLen qLen key).params
        · by_cases hk : keyValid (publicKeyBytes pLen qLen key) = true
          · simp [verifyBytes,validatePublicKeyBytes,hw,hl,hs,hp,hk]
          · have hk' : keyValid (publicKeyBytes pLen qLen key) = false := Bool.eq_false_iff.mpr hk
            have hu : {publicKeyBytes pLen qLen key with x := none} = publicKeyBytes pLen qLen key := rfl
            simp [verifyBytes,validatePublicKeyBytes,verify,hw,hl,hs,hp,hk',hu]
        · simp [verifyBytes,validatePublicKeyBytes,hw,hl,hs,hp]
      · simp [verifyBytes,hs]
    · simp [verifyBytes,validatePublicKeyBytes,hl]
  · simp [verifyBytes,validatePublicKeyBytes,hw]

theorem verifyBytes_invalid_public (pLen qLen : Nat) (key signature digest : List VG.Byte)
    (h : validatePublicKeyBytes pLen qLen key = false) :
    verifyBytes pLen qLen key signature digest = false := by
  rw [verifyBytes_validation, h]
  rfl

end VG.Proof.Dsa
