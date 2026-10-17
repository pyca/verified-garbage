module

public import VerifiedGarbage.Proof.Dsa.X86.AcceptedSpec
public import VerifiedGarbage.Proof.Dsa.SignVerify

/-! # Connecting the x86 verification formula to the packed-byte contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG

theorem verifyBytes_compute {pLen qLen p q g y rv sv n : Nat} {key signature digest : List Byte}
    (widths : Spec.Dsa.lengthsValid pLen qLen) (shape : shapeValid p q)
    (keyLen : key.length = 3 * pLen + qLen) (sigLen : signature.length = 2 * qLen)
    (keyValue : Spec.Dsa.publicKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, none⟩)
    (rValue : Spec.Dsa.decodeBE (signature.take qLen) = rv)
    (sValue : Spec.Dsa.decodeBE (signature.drop qLen) = sv)
    (qBits : Spec.Dsa.bitLength q = 8 * n) :
    let computed := (g ^ (Spec.Dsa.decodeBE (digest.take n) % q * (sv ^ (q - 2) % q) % q) % p *
      (y ^ (rv * (sv ^ (q - 2) % q) % q) % p) % p) % q
    Spec.Dsa.verifyBytes pLen qLen key signature digest =
      decide (publicChecks p q g y ∧ (0 < rv ∧ rv < q) ∧ (0 < sv ∧ sv < q) ∧ computed = rv) := by
  dsimp only
  let K : Spec.Dsa.Key := ⟨⟨p, q, g⟩, y, none⟩
  let computed := (g ^ (Spec.Dsa.decodeBE (digest.take n) % q * (sv ^ (q - 2) % q) % q) % p *
      (y ^ (rv * (sv ^ (q - 2) % q) % q) % p) % p) % q
  have reduced := VG.Proof.Dsa.verify_reduced K ⟨rv, sv⟩ digest n qBits
  simp only [K, ← VG.Proof.Dsa.powMod_rsa, VG.Proof.Dsa.powMod_eq] at reduced
  simp only [publicChecks_spec shape]
  unfold Spec.Dsa.verifyBytes
  simp only [widths, decide_true, Bool.not_true, keyLen, sigLen, bne_self_eq_false,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, keyValue, rValue, sValue]
  rw [reduced]
  change (decide (Spec.Dsa.parametersValid K.params) &&
    (if !Spec.Dsa.keyValid K || !(0 < rv && rv < q && 0 < sv && sv < q) then false else computed == rv)) =
      decide ((Spec.Dsa.parametersValid K.params ∧ Spec.Dsa.keyValid K = true) ∧
        (0 < rv ∧ rv < q) ∧ (0 < sv ∧ sv < q) ∧ computed = rv)
  by_cases P : Spec.Dsa.parametersValid K.params <;> cases V : Spec.Dsa.keyValid K <;>
    by_cases R : 0 < rv ∧ rv < q <;> by_cases S : 0 < sv ∧ sv < q <;> by_cases E : computed = rv <;>
    simp_all [← Bool.decide_and, and_assoc]

end VG.Proof.Dsa.X86
