import VerifiedGarbage.Proof.X25519.X86.Field32.CallTaint
import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-! The summary of `vg_gf25519_r32_pow250` (see `Field32/CallTaint`). -/

namespace VG.Proof.X25519.X86

taint_summary pow250Sum : VG.X86.taint τCall
  (.call Spec.X25519.Field32.pow250Api.name Impl.X25519.X86.Field32.pow250Fn)

end VG.Proof.X25519.X86
