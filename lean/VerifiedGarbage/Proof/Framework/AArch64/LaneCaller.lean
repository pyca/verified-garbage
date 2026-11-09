module

public import VerifiedGarbage.Proof.Framework.AArch64.LaneTaint
public import VerifiedGarbage.Proof.Framework.RelCT

/-! Caller-facing adapters for vector-aware constant-time analysis.
Initial vectors are secret, so callers only need their existing public-GPR facts.
-/

@[expose] public section

namespace VG.AArch64.LaneTaint

theorem agree_initial {τ : AArch64.Taint.T} {x y : State}
    (h : AArch64.Taint.Agree τ x y) : Agree (τ, empty) x y :=
  ⟨h, fun b r hr => by cases b <;> exact False.elim (RegSet.not_mem_empty r hr)⟩

theorem constantTime {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog isa}
    (τ : AArch64.Taint.T)
    (hp : ∀ x y, Pre x → Pre y → Pub x y → AArch64.Taint.Agree τ x y)
    {hc : VG.Taint.Hint T}
    (h : (taint.check (τ, empty) c hc).isSome = true) : ConstantTime isa Pre Pub c :=
  VG.Taint.constantTime (A := taint) (τ, empty)
    (fun x y hx hy hxy => agree_initial (hp x y hx hy hxy)) h

end VG.AArch64.LaneTaint
