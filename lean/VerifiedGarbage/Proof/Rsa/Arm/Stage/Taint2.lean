module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyFrame
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.KeyFrame
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The ARMv7 key stages: the pieces of Montgomery multiplication's setup the taint analysis checks -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover

/-- The registers of the working space's context. -/
abbrev ctxRegs : List Reg := [.r7, .r8, .r9]

end VG.Proof.Rsa.Arm.Recover
