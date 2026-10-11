import VerifiedGarbage.Impl.Blowfish.X86
import VerifiedGarbage.Proof.Framework.X86.Lit

/-! Literal code keeps the unrolled S-box scans cheap for kernel-evaluated audits. -/
namespace VG.Impl.Blowfish.X86
materialize_code encrypt
materialize_code decrypt
end VG.Impl.Blowfish.X86
