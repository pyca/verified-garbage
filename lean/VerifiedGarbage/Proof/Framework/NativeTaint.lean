module

public meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! `native_taint_decide` (`NativeTaintCore.lean`) for the x86 analysis
`X86.taint`, with its compiled copy (`X86/NativeHintData.lean`). -/
