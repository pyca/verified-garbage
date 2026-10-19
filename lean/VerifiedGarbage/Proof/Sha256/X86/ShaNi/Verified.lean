module

import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Whole
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Whole
public import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Sha256.X86.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.MdStream.X86
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Compress
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Load
meta import VerifiedGarbage.Impl.MdStream.X86
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Compress
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Load

@[expose] public section

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86

theorem compress_verified :
    Verified X86.target Impl.Sha256.X86.ShaNi.compress Proof.Sha256.compressX86 :=
  ⟨fun s hs => correct (VG.Proof.Sha256.X86.pre_of s hs),
    VG.Taint.constantTime (A := sseTaint) VG.Proof.Sha256.X86.τ₀
      (fun _ _ h₁ h₂ hpub => VG.Proof.Sha256.X86.agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨VG.Proof.Sha256.X86.satState, VG.Proof.Sha256.X86.sat_pre⟩⟩

theorem compress_nosp : NoSp Impl.Sha256.X86.ShaNi.compress := NoSp.of_all (by lit_decide)
theorem compress_stack : stackUse Impl.Sha256.X86.ShaNi.compress = 0 := by lit_decide

end VG.Proof.Sha256.X86.ShaNi
