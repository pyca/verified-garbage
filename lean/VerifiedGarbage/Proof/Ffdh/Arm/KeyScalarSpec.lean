module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! The native cut encoding is the scalar required by the shared FFDH specification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

def scalarOctets (p : Inputs) (rb : List Byte) : List Byte :=
  VG.Proof.Ffdh.KeyScalar.cut rb p.scalarLead (p.scalarMask.setWidth 8)

theorem scalarOctets_length {p : Inputs} {rb : List Byte} (size : rb.length = p.k) :
    (scalarOctets p rb).length = p.k := by
  rw [scalarOctets, VG.Proof.Ffdh.KeyScalar.cut_length _ (by have := p.scalarLeadBound; omega), size]

theorem scalarOctets_value {p : Inputs} {rb : List Byte} (size : rb.length = p.k)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    Spec.Rsa.os2ip (scalarOctets p rb) = Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb := by
  unfold scalarOctets
  apply VG.Proof.Ffdh.KeyScalar.cut_eq (by have := p.minLength; omega) p.domainLengths
    (fun _ => ⟨odd, large⟩) size
  have bound : p.scalarLead < p.boundOctets.length := by rw [p.boundOctetsLength]; exact p.scalarLeadBound
  have byteEq : p.boundOctets.getD p.scalarLead 0 = p.boundOctets[p.scalarLead] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some]
  change ((BitVec.ofNat 32 (VG.Proof.Ffdh.KeyScalar.smearN (p.boundOctets.getD p.scalarLead 0).toNat)).setWidth 8).toNat = _
  rw [BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 32), BitVec.toNat_ofNat, Nat.mod_eq_of_lt
    (VG.Proof.Ffdh.KeyScalar.smearN_lt _ (p.boundOctets.getD p.scalarLead 0).isLt),
    VG.Proof.Ffdh.KeyScalar.smearN_eq _ (p.boundOctets.getD p.scalarLead 0).isLt, byteEq]
  rfl

theorem scalarOctets_significant {p : Inputs} {rb : List Byte} :
    Spec.Rsa.os2ip ((scalarOctets p rb).drop p.scalarLead) = Spec.Rsa.os2ip (scalarOctets p rb) :=
  VG.Proof.Ffdh.KeyScalar.os2ip_cut_drop _ _ _

end VG.Proof.Ffdh.Arm
