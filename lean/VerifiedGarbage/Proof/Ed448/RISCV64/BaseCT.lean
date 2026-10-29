module

public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# Ed448's base-point multiplication on RISCV64: constant time

Only the pointers in `a0`–`a2` are public; the taint analysis
(`taint_decide`) finds that every branch and address depends on them and on
the loop counters alone. The bits of the scalar select points only by masks.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64

theorem scalarBase_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2], s₁.gpr r = s₂.gpr r) :
    ConstantTime isa Pre Pub Impl.Ed448.RISCV64.scalarBase :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun s₁ s₂ h₁ h₂ hp => by
      obtain ⟨hsp, hr⟩ := hpub s₁ s₂ h₁ h₂ hp
      exact ⟨hsp, fun r h => hr r (by simpa using h)⟩) (by taint_decide)

end VG.Proof.Ed448.RISCV64
