module

public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTail
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarUpper

/-! Key-attempt results parameterized by their public scalar layout. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

def sampleScalarValid (p : Inputs) (l : ScalarLayout p) (rb : List Byte) : Prop :=
  0 < Spec.Rsa.os2ip (l.encode rb) ∧ Spec.Rsa.os2ip (l.encode rb) < scalarBound p

instance (p : Inputs) (l : ScalarLayout p) (rb : List Byte) : Decidable (sampleScalarValid p l rb) :=
  inferInstanceAs (Decidable (_ ∧ _))

def sampleSuccess (p : Inputs) (l : ScalarLayout p) (rb : List Byte) : Bool :=
  decide (sampleScalarValid p l rb) && keyAccepted p (l.encode rb)

def sampleMainFlag (p : Inputs) (l : ScalarLayout p) (rb : List Byte) : BitVec 32 :=
  if sampleScalarValid p l rb then (if keyAccepted p (l.encode rb) then 1 else 3) else 2

def sampleResult (p : Inputs) (l : ScalarLayout p) (rb : List Byte) (s : State) : Prop :=
  s.gpr .r0 = sampleMainFlag p l rb ∧
  Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.k =
    (if sampleSuccess p l rb then l.encode rb else List.replicate p.k 0) ∧
  Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k =
    (if sampleSuccess p l rb then Spec.Rsa.i2osp (keyPower p (l.encode rb)) p.k else List.replicate p.k 0)

end VG.Proof.Ffdh.Arm
