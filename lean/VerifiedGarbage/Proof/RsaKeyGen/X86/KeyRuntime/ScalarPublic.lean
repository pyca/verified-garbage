module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.Key

/-! # The unchanged scalar failure and retry paths preserve public arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key

theorem dZero_public : Public dZero := by
  refine of_check (hint := ?hint) ?check ?lower
  case check => taint_decide
  case lower => taint_decide

theorem retry_public : Public retry := by
  refine of_check (hint := ?hint) ?check ?lower
  case check => taint_decide
  case lower => taint_decide

end VG.Proof.RsaKeyGen.X86.KeyRuntime
