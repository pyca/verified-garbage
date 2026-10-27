module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# Ed25519's scalar functions on RISC-V: constant time

Only the pointers are public; the taint analysis (`taint_decide`) finds that
every branch and address depends on them and on the loop counters alone. The
bytes of the scalars select the remainder only by masks.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64

theorem scalarReduce_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2], s₁.gpr r = s₂.gpr r) :
    ConstantTime isa Pre Pub Impl.Ed25519.RISCV64.scalarReduce :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun s₁ s₂ h₁ h₂ hp => by
      obtain ⟨hsp, hr⟩ := hpub s₁ s₂ h₁ h₂ hp
      exact ⟨hsp, fun r h => hr r (by simpa using h)⟩) (by taint_decide)

theorem scalarMulAdd_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4], s₁.gpr r = s₂.gpr r) :
    ConstantTime isa Pre Pub Impl.Ed25519.RISCV64.scalarMulAdd :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun s₁ s₂ h₁ h₂ hp => by
      obtain ⟨hsp, hr⟩ := hpub s₁ s₂ h₁ h₂ hp
      exact ⟨hsp, fun r h => hr r (by simpa using h)⟩) (by taint_decide)

end VG.Proof.Ed25519.RISCV64
