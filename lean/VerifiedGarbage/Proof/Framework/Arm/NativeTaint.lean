module
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.RegionsSub


/-! `native_taint_decide` for the ARMv7 analysis `Arm.taint`: its hints are
computed by the compiled copy of the domain (`Arm/NativeHintData.lean`) and
checked by the kernel like any other. -/
