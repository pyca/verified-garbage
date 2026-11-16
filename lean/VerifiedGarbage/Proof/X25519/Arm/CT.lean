module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.X25519.Arm.Lit
public import VerifiedGarbage.Impl.X25519.Arm
public import VerifiedGarbage.Impl.X25519.Arm.Words
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.X25519.Arm.Lit
meta import VerifiedGarbage.Impl.X25519.Arm
meta import VerifiedGarbage.Impl.X25519.Arm.Words
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# X25519 on 32-bit ARM: constant time

Only the pointers in `r0`–`r3` are public; the taint analysis (`taint_decide`)
finds that every branch and address depends on them and on the loop counters
alone. `vg_x25519_umaal` keeps its counter and `out` in the working space, the
second writable region, whose base the analysis knows in `r3` (`umaalTaint`),
so that what it stores of them there is public when it loads it again; its
`umaal`s make the registers they write secret (`taintU`).
-/

@[expose] public section

namespace VG.Proof.X25519.Arm

open VG VG.Arm

theorem x25519_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → ∀ r ∈ [Reg.r0, .r1, .r2, .r3], s₁.gpr r = s₂.gpr r) :
    ConstantTime isa Pre Pub Impl.X25519.Arm.x25519 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s₁ s₂ h₁ h₂ hp => Taint.agree_ofRegs (hpub s₁ s₂ h₁ h₂ hp)) (by taint_decide)

/-- `vg_x25519_umaal`'s: the arguments are public; `out` is 32 bytes and the
working space 4096, at `r3`. -/
def umaalTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [32, 4096], bases := [(.r3, 1)] }

theorem x25519Umaal_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hagree : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → VG.Arm.Taint.Agree umaalTaint s₁ s₂) :
    ConstantTime isa Pre Pub Impl.X25519.Arm.Words.x25519Umaal :=
  VG.Taint.constantTime (A := taintU) umaalTaint hagree (by taint_decide)

end VG.Proof.X25519.Arm
