module

public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # The generation checks in the order of the x86 implementation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG

theorem deriveSpec {pLen qLen p q g x : Nat} {params scalar : List Byte}
    (widths : Spec.Dsa.lengthsValid pLen qLen)
    (paramsLen : params.length = 2 * pLen + qLen) (scalarLen : scalar.length = qLen)
    (paramsValue : Spec.Dsa.paramsBytes pLen qLen params = ⟨p, q, g⟩)
    (scalarValue : Spec.Dsa.decodeBE scalar = x) :
    Spec.Dsa.deriveKeyBytes pLen qLen params scalar =
      if shapeValid p q ∧ (((1 < g ∧ g < p) ∧ (p - 1) % q = 0 ∧ g ^ q % p = 1) ∧
        (0 < x ∧ x < q) ∧ (1 < g ^ x % p ∧ g ^ x % p < p))
      then some (params ++ Spec.Dsa.encodeBE pLen (g ^ x % p) ++ scalar) else none := by
  rw [deriveKeyBytes_eq widths paramsLen scalarLen]
  simp only [paramsValue, scalarValue, powMod_eq, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  congr 1
  simp only [shapeValid, and_assoc, and_comm, and_left_comm]

end VG.Proof.Dsa.X86
