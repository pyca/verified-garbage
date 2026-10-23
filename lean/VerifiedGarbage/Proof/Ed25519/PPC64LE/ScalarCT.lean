module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Scalar
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Ed25519.PPC64LE.Scalar
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# Ed25519's scalar functions on PPC64LE: constant time

Only the pointers are public; the taint analysis (`taint_decide`) finds that
every branch and address depends on them and on the loop counters alone. The
bytes of the scalars select the remainder only by masks.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE

theorem scalarReduce_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r3, .r4, .r5], s₁.gpr r = s₂.gpr r) :
    ConstantTime isa Pre Pub Impl.Ed25519.PPC64LE.scalarReduce :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun s₁ s₂ h₁ h₂ hp => by
      obtain ⟨hsp, hr⟩ := hpub s₁ s₂ h₁ h₂ hp
      exact ⟨hsp, fun r h => hr r (by simpa using h)⟩) (by taint_decide)

theorem scalarMulAdd_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], s₁.gpr r = s₂.gpr r) :
    ConstantTime isa Pre Pub Impl.Ed25519.PPC64LE.scalarMulAdd :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun s₁ s₂ h₁ h₂ hp => by
      obtain ⟨hsp, hr⟩ := hpub s₁ s₂ h₁ h₂ hp
      exact ⟨hsp, fun r h => hr r (by simpa using h)⟩) (by taint_decide)

end VG.Proof.Ed25519.PPC64LE
