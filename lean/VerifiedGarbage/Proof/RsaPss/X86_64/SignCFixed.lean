module
public import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
public import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
meta import VerifiedGarbage.Impl.RsaPss.X86_64.Encoding
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-!
# RSASSA-PSS signing and verification on x86-64, around the encoding: the
taint checks of their own pieces
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64

/-- The checks. -/
structure SCFixed : Prop where
  prep : ∃ hc, (taint.check (pT 2 [17, 21, 22, 37, 39, 40] [.rax]) (.block (emBitsB ++ encArgs)) hc).isSome = true
  test : ∃ hc, (taint.check (pT 2 [] []) (.block [.alu32 .test .rax (.reg .rax)]) hc).isSome = true

theorem scFixed : SCFixed := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- Verification's. -/
structure VCFixed : Prop where
  prep : ∃ hc, (taint.check (pT 1 [17, 19, 20, 21, 22, 38] [.rax]) (.block (emBitsB ++ pubArgsC)) hc).isSome = true
  chkArgs : ∃ hc, (taint.check (pT 1 ([17, 21, 22, 37] ++ [26, 27, 28]) []) (.block chkArgs) hc).isSome = true
  acc : ∃ hc, (taint.check (pT 1 [] []) (.block [.alu .and .rax (.mem (sp sAcc))]) hc).isSome = true

theorem vcFixed : VCFixed := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64
