module

public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# Ed448's verification equation on RISCV64: constant time

Only the pointers in `a0`–`a3` are public; the taint analysis
(`taint_decide`) finds that every branch and address depends on them and on
the loop counters alone. The contract declares the inputs public too, which
this does not need.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64

theorem verifyEquation_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2, .a3], s₁.gpr r = s₂.gpr r) :
    ConstantTime isa Pre Pub Impl.Ed448.RISCV64.verifyEquation :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun s₁ s₂ h₁ h₂ hp => by
      obtain ⟨hsp, hr⟩ := hpub s₁ s₂ h₁ h₂ hp
      exact ⟨hsp, fun r h => hr r (by simpa using h)⟩) (by taint_decide)

end VG.Proof.Ed448.RISCV64
