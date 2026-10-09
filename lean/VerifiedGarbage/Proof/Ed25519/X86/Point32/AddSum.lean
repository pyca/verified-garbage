import VerifiedGarbage.Proof.X25519.X86.Field32.CallTaint
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-! The summary of `vg_ed25519_r32_point_add` (see `X25519/X86/Field32/CallTaint`), which
keeps `esi`, the callers' loop counter. -/

namespace VG.Proof.Ed25519.X86

taint_summary addSum : VG.X86.taint X25519.X86.τCall
  (.call Spec.Ed25519.Point32.addApi.name Impl.Ed25519.X86.Point32.addFn)
  keeping ({ regs := .ofList [.esi], flags := false } : VG.X86.Taint.T)

end VG.Proof.Ed25519.X86
