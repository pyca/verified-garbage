module

import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Rc2.AArch64.Lit
public import VerifiedGarbage.Impl.Rc2.AArch64.ExpandKey
public import VerifiedGarbage.Impl.Rc2.AArch64.Block
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Rc2.AArch64.Lit
meta import VerifiedGarbage.Impl.Rc2.AArch64.ExpandKey
meta import VerifiedGarbage.Impl.Rc2.AArch64.Block

/-! # Constant-time RC2 block and key-expansion programs -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

/-- Only argument pointers and explicitly public integer parameters agree;
all memory contents, including the key, schedule, and data, may differ. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

end VG.Proof.Rc2.AArch64
