import VerifiedGarbage.Proof.X25519.X86.Field32.CallTaint
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-! The summaries of `vg_ed25519_r32_point_add` and `_add_affine` (see
`X25519/X86/Field32/CallTaint`), which keep `esi`, the callers' loop counter. The comb calls
`_add_affine` in its loop, with the tables' address at byte 1160 of the workspace (`combTbl`)
public too (`τCallTbl`), which it reads again after the call. -/

namespace VG.Proof.Ed25519.X86

taint_summary addSum : VG.X86.taint X25519.X86.τCall
  (.call Spec.Ed25519.Point32.addApi.name Impl.Ed25519.X86.Point32.addFn)
  keeping ({ regs := .ofList [.esi], flags := false } : VG.X86.Taint.T)

/-- `τCall`, with the tables' address at byte 1160 of the workspace (`combTbl`) public too: what
is public before the comb's calls, in its loops. -/
def τCallTbl : VG.X86.Taint.T := { X25519.X86.τCall with slots := VG.Slots.ofList [(0, 0, 4), (2, 1160, 4)] }

taint_summary affSum : VG.X86.taint τCallTbl
  (.call Spec.Ed25519.Point32.addAffineApi.name Impl.Ed25519.X86.Point32.affFn)
  keeping ({ regs := .ofList [.esi], flags := false } : VG.X86.Taint.T)

end VG.Proof.Ed25519.X86
