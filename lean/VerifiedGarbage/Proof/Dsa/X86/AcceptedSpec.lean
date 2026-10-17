module

public import VerifiedGarbage.Proof.Dsa.X86.PublicKey
public import VerifiedGarbage.Proof.Dsa.X86.Shape
public import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # Post-shape acceptance agrees with the DSA domain and key predicates -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG

theorem publicChecks_spec {p q g y : Nat} (H : shapeValid p q) :
    publicChecks p q g y ↔
      Spec.Dsa.parametersValid ⟨p, q, g⟩ ∧ Spec.Dsa.keyValid ⟨⟨p, q, g⟩, y, none⟩ = true := by
  have B := VG.Proof.Dsa.supported_bounds H.1
  simp only [publicChecks, Spec.Dsa.parametersValid, Spec.Dsa.keyValid, VG.Proof.Dsa.powMod_eq,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_true]
  constructor
  · rintro ⟨⟨G, Y⟩, D, GP, YP⟩
    exact ⟨⟨H.1, H.2.2, H.2.1, B.2.2, D, G.1, G.2, GP⟩, ⟨Y.1, Y.2⟩, YP⟩
  · rintro ⟨P, ⟨Ylo, Yhi⟩, YP⟩
    exact ⟨⟨⟨P.2.2.2.2.2.1, P.2.2.2.2.2.2.1⟩, Ylo, Yhi⟩, P.2.2.2.2.1, P.2.2.2.2.2.2.2, YP⟩

theorem privateChecks_spec {p q g y x : Nat} (H : shapeValid p q) :
    (publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ g ^ x % p = y) ↔
      Spec.Dsa.parametersValid ⟨p, q, g⟩ ∧ Spec.Dsa.keyValid ⟨⟨p, q, g⟩, y, some x⟩ = true := by
  rw [publicChecks_spec H]
  simp only [Spec.Dsa.keyValid, VG.Proof.Dsa.powMod_eq, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, and_true]
  simp only [and_assoc]

end VG.Proof.Dsa.X86
