module

public import VerifiedGarbage.Proof.Dsa.X86.Shape
public import VerifiedGarbage.Spec.Dsa.SignVerify

/-! # Public-shape rejection agrees with both packed-byte specifications -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG

theorem parametersValid_shape {p q g : Nat} (H : Spec.Dsa.parametersValid ⟨p, q, g⟩) : shapeValid p q :=
  ⟨H.1, H.2.2.1, H.2.1⟩

theorem signBytes_invalid_shape {pLen qLen : Nat} {key nonce digest : List Byte}
    (H : ¬ shapeValid (Spec.Dsa.privateKeyBytes pLen qLen key).params.p
      (Spec.Dsa.privateKeyBytes pLen qLen key).params.q) :
    Spec.Dsa.signBytes pLen qLen key nonce digest = none := by
  have invalid : ¬ Spec.Dsa.parametersValid (Spec.Dsa.privateKeyBytes pLen qLen key).params :=
    fun P => H (parametersValid_shape P)
  unfold Spec.Dsa.signBytes
  split
  · rfl
  · simp only [invalid, decide_false, Bool.not_false, ↓reduceIte]

theorem verifyBytes_invalid_shape {pLen qLen : Nat} {key signature digest : List Byte}
    (H : ¬ shapeValid (Spec.Dsa.publicKeyBytes pLen qLen key).params.p
      (Spec.Dsa.publicKeyBytes pLen qLen key).params.q) :
    Spec.Dsa.verifyBytes pLen qLen key signature digest = false := by
  have invalid : ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes pLen qLen key).params :=
    fun P => H (parametersValid_shape P)
  unfold Spec.Dsa.verifyBytes
  split
  · rfl
  · simp only [invalid, decide_false, Bool.false_and]

end VG.Proof.Dsa.X86
