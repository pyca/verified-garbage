module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The fixed LCM schedule keeps the factors secret. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem lcm_public : Public lcmPart := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

end VG.Proof.RsaKeyGen.X86.KeyRuntime
