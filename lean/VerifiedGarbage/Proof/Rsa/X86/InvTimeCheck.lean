module

public import VerifiedGarbage.Proof.Rsa.X86.InvTimeBase
meta import VerifiedGarbage.Proof.Rsa.X86.InvTimeBase
meta import VerifiedGarbage.Impl.Rsa.X86.KeyRt
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import Init.Data.Option.Basic
meta import Init.Data.Option.Basic
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
meta import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt

/-! # The general inverse fallback has its original public-argument trace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvTiming
open VG VG.X86
 theorem fallback_check :
    ∃ hint,(VG.Taint.check sseTaint τ (VG.Impl.Rsa.X86.KeyRt.inverse VG.Impl.Rsa.X86.CrtValuesRt.lay)
      hint).isSome=true := ⟨_, by taint_decide⟩
end VG.Proof.Rsa.X86.InvTiming
