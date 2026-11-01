module

public import VerifiedGarbage.Proof.X25519.X86.Field32.CallTaint
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
public import VerifiedGarbage.Impl.Ed25519.X86.Point32
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.X86.Field32.CallTaint
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
meta import VerifiedGarbage.Impl.Ed25519.X86.Point32
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The summaries of `vg_ed25519_r32_point_add` and `_add_affine` (see
`X25519/X86/Field32/CallTaint`), which keep `esi`, the callers' loop counter. The comb calls
`_add_affine` in its loop, with the tables' address at byte 1160 of the workspace (`combTbl`)
public too (`τCallTbl`), which it reads again after the call. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86

taint_summary addSum : VG.X86.taint X25519.X86.τCall
  (.call "vg_ed25519_r32_point_add" Impl.Ed25519.X86.Point32.addFn)
  keeping ({ regs := .ofList [.esi], flags := false } : VG.X86.Taint.T)

/-- `τCall`, with the tables' address at byte 1160 of the workspace (`combTbl`) public too: what
is public before the comb's calls, in its loops. -/
def τCallTbl : VG.X86.Taint.T := { X25519.X86.τCall with slots := VG.Slots.ofList [(0, 0, 4), (2, 1160, 4)] }

taint_summary affSum : VG.X86.taint τCallTbl
  (.call "vg_ed25519_r32_add_affine" Impl.Ed25519.X86.Point32.affFn)
  keeping ({ regs := .ofList [.esi], flags := false } : VG.X86.Taint.T)

end VG.Proof.Ed25519.X86
