module

import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.X25519.Arm.Lit
import VerifiedGarbage.Proof.X25519.Arm.UmaalTaint
public import VerifiedGarbage.Impl.X25519.Arm
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.X25519.Arm.Lit
meta import VerifiedGarbage.Proof.X25519.Arm.UmaalTaint
meta import VerifiedGarbage.Impl.X25519.Arm
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# X25519 on 32-bit ARM: constant time

Only the pointers in `r0`–`r3` are public; the taint analysis (`taint_decide`)
finds that every branch and address depends on them and on the loop counters
alone; for `vg_x25519_umaal`, with `umaal` making the registers it writes
secret (`UmaalTaint`).
-/

@[expose] public section

namespace VG.Proof.X25519.Arm

open VG VG.Arm

theorem x25519_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → ∀ r ∈ [Reg.r0, .r1, .r2, .r3], s₁.gpr r = s₂.gpr r) :
    ConstantTime isa Pre Pub Impl.X25519.Arm.x25519 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s₁ s₂ h₁ h₂ hp => Taint.agree_ofRegs (hpub s₁ s₂ h₁ h₂ hp)) (by taint_decide)

theorem x25519Umaal_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → ∀ r ∈ [Reg.r0, .r1, .r2, .r3], s₁.gpr r = s₂.gpr r) :
    ConstantTime isa Pre Pub Impl.X25519.Arm.x25519Umaal :=
  VG.Taint.constantTime (A := UmaalTaint.analysis) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s₁ s₂ h₁ h₂ hp => Taint.agree_ofRegs (hpub s₁ s₂ h₁ h₂ hp)) (by taint_decide)

end VG.Proof.X25519.Arm
