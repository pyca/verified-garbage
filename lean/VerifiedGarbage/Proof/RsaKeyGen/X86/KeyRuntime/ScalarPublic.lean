module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO

/-! # The unchanged scalar failure and retry paths preserve public arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key

theorem dZero_public : Public dZero := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

theorem retry_public : Public retry := by
  refine of_any (hint := ?hint) ?check
  case check => taint_decide

end VG.Proof.RsaKeyGen.X86.KeyRuntime
