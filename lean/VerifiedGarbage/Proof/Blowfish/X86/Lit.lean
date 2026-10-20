module

public import VerifiedGarbage.Impl.Blowfish.X86
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blowfish.X86
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! Literal code keeps the unrolled S-box scans cheap for kernel-evaluated audits. -/

@[expose] public section

namespace VG.Impl.Blowfish.X86
materialize_code encrypt
materialize_code decrypt
end VG.Impl.Blowfish.X86
