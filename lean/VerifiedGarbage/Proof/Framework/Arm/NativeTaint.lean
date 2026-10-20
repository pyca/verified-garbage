module

public meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
public meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! `native_taint_decide` for the ARMv7 analysis `Arm.taint`: its hints are
computed by the compiled copy of the domain (`Arm/NativeHintData.lean`) and
checked by the kernel like any other. -/
