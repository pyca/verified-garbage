module

import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Whole
public import VerifiedGarbage.Proof.Sha256.X86.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
public import VerifiedGarbage.Impl.Sha256.X86.ShaNi
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Whole
meta import VerifiedGarbage.Proof.Sha256.X86.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
meta import VerifiedGarbage.Impl.Sha256.X86.ShaNi
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

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
