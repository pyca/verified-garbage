module

public import VerifiedGarbage.Impl.X25519.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.X25519.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# X25519 on PPC64LE: constant time

Only the pointers in `r3`–`r6` are public; the taint analysis (`taint_decide`)
finds that every branch and address depends on them and on the loop counters
alone.
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE

theorem x25519_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r3, .r4, .r5, .r6], s₁.gpr r = s₂.gpr r) :
    ConstantTime isa Pre Pub Impl.X25519.PPC64LE.x25519 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun s₁ s₂ h₁ h₂ hp => by
      obtain ⟨hsp, hr⟩ := hpub s₁ s₂ h₁ h₂ hp
      exact ⟨hsp, fun r h => hr r (by simpa using h)⟩) (by taint_decide)

end VG.Proof.X25519.PPC64LE
