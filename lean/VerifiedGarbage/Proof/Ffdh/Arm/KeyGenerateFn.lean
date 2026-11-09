module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate

import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
/-! AAPCS key generation from caller-provided entropy with native rejection. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure KeyGenerateFnInput (p : Inputs) (rb : List Byte) (s : State) : Prop extends KeyFnInput p rb s where
  calls : KeyCallMemory p (entered s)
  savedCall : (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint (FrameStack.belowA (entered s).sp 48)

end VG.Proof.Ffdh.Arm
