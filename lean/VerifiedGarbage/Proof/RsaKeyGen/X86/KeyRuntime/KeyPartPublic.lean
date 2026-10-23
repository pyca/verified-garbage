module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The CRT and final checks keep the factors secret. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem keyPart_public : Public keyPart := by
  refine of_check (hint := ?hint) ?check ?lower
  case check => taint_decide
  case lower => taint_decide

end VG.Proof.RsaKeyGen.X86.KeyRuntime
