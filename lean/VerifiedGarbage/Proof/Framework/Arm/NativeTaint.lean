module

public import VerifiedGarbage.Proof.Framework.NativeTaintCore
public meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-! `native_taint_decide` for the ARMv7 analysis `Arm.taint`: its hints are
computed by the compiled copy of the domain (`Arm/NativeHintData.lean`) and
checked by the kernel like any other. -/
