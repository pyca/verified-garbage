module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! The native cut encoding is the scalar required by the shared FFDH specification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

def scalarOctets (p : Inputs) (rb : List Byte) : List Byte :=
  VG.Proof.Ffdh.KeyScalar.cut rb p.scalarLead (p.scalarMask.setWidth 8)

end VG.Proof.Ffdh.Arm
