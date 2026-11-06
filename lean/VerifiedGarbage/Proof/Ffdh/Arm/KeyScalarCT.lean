module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

import VerifiedGarbage.Proof.Ffdh.Arm.KeyBoundCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyArgsCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyBound
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeyByteCT
/-! The complete scalar sampler leaks only the public domain bound and buffer layout. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure KeyScalarInput (p : Inputs) (slots : List Nat) (rb : List Byte) (s : State) : Prop where
  context : Context p slots s
  entropy : Octets p.base p.entropy p.len rb s
  outputs : KeyOutputs p s
  entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩

end VG.Proof.Ffdh.Arm
