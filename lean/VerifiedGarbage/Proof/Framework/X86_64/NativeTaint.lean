module

public import VerifiedGarbage.Proof.Framework.NativeTaintCore
public meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.X86_64.NativeHintData
public meta import VerifiedGarbage.Proof.Framework.X86_64.NativeHintData

/-! `native_taint_decide` for the x86-64 analysis `X86_64.taint`: its hints
are computed by the compiled copy of the domain (`X86_64/NativeHintData.lean`)
and checked by the kernel like any other. -/
