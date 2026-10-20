module

public import VerifiedGarbage.Proof.Dsa.AArch64.DomainShape
public import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.DomainWidths
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Public shape acceptance and early rejection in the DSA specification -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG

theorem decodeBE_last_parity (bs : List Byte) (hn : 0 < bs.length) :
    Spec.Dsa.decodeBE bs % 2 = (bs[bs.length - 1]'(by omega)).toNat % 2 := by
  have hne : bs ≠ [] := by intro h; simp only [h, List.length_nil, Nat.lt_irrefl] at hn
  have he := VG.Proof.Dsa.decodeBE_last_mod_two bs.dropLast (bs.getLast hne)
  rw [List.dropLast_concat_getLast hne, List.getLast_eq_getElem] at he
  exact he

def shapeAccepted (p q : List Byte) (hp : 0 < p.length) (hq : 0 < q.length) : Bool :=
  shapeValid p q (p[p.length - 1]'(by omega)) (q[q.length - 1]'(by omega))

theorem shapeAccepted_spec (p q : List Byte) (hp : 0 < p.length) (hq : 0 < q.length) :
    shapeAccepted p q hp hq = decide (
      Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
        (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q)) ∧
      Spec.Dsa.decodeBE p % 2 = 1 ∧ Spec.Dsa.decodeBE q % 2 = 1) := by
  unfold shapeAccepted
  rw [shapeValid_spec, ← decodeBE_last_parity p hp, ← decodeBE_last_parity q hq]

theorem shapeAccepted_false {p q : List Byte} {hp : 0 < p.length} {hq : 0 < q.length}
    (h : shapeAccepted p q hp hq = false) (g : Nat) :
    ¬ Spec.Dsa.parametersValid ⟨Spec.Dsa.decodeBE p, Spec.Dsa.decodeBE q, g⟩ := by
  rw [shapeAccepted_spec] at h
  intro hv
  have ht : decide (Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q)) ∧
      Spec.Dsa.decodeBE p % 2 = 1 ∧ Spec.Dsa.decodeBE q % 2 = 1) = true :=
    decide_eq_true ⟨hv.1, hv.2.1, hv.2.2.1⟩
  rw [h] at ht
  cases ht

theorem signBytes_invalid_shape {pLen qLen : Nat} {key nonce digest : List Byte}
    (h : ¬ Spec.Dsa.parametersValid (Spec.Dsa.privateKeyBytes pLen qLen key).params) :
    Spec.Dsa.signBytes pLen qLen key nonce digest = none := by
  unfold Spec.Dsa.signBytes
  split
  · rfl
  · simp only [h, decide_false, Bool.not_false, ↓reduceIte]

theorem verifyBytes_invalid_shape {pLen qLen : Nat} {key signature digest : List Byte}
    (h : ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes pLen qLen key).params) :
    Spec.Dsa.verifyBytes pLen qLen key signature digest = false := by
  unfold Spec.Dsa.verifyBytes
  split
  · rfl
  · simp only [h, decide_false, Bool.false_and]

end VG.Proof.Dsa.AArch64
