module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedPre

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Sign (signRootConsts)

/-- A verification function on `μ`, with both immutable transform tables,
that `verify_message_cached` can call. -/
structure VerifyFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified target c (verifyContract p (abi.withConsts signRootConsts) 16)
  dle : DLe 1 c

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
