module

public import VerifiedGarbage.Proof.X25519.X86.Field32.CallTaint
meta import VerifiedGarbage.Proof.X25519.X86.Field32.CallTaint
public import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! The summary of `vg_gf25519_r32_pow250` (see `Field32/CallTaint`). -/

@[expose] public section

namespace VG.Proof.X25519.X86

taint_summary pow250Sum : VG.X86.taint τCall
  (.call Spec.X25519.Field32.pow250Api.name Impl.X25519.X86.Field32.pow250Fn)

end VG.Proof.X25519.X86
