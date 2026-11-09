module

import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Rc2.Arm.Lit
public import VerifiedGarbage.Impl.Rc2.Arm.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Rc2.Arm.Lit
meta import VerifiedGarbage.Impl.Rc2.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time RC2 block operations -/

@[expose] public section

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

end VG.Proof.Rc2.Arm
