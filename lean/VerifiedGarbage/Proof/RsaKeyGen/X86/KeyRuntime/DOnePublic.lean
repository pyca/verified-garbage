module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public

/-! # The unit-exponent path has public control flow. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem dOne_public : Public dOne := by
  refine of_check (hint := ?hint) ?check ?lower
  case check => taint_decide
  case lower => taint_decide

end VG.Proof.RsaKeyGen.X86.KeyRuntime
