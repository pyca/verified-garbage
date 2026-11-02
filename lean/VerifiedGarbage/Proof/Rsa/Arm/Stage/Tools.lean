module

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont
import VerifiedGarbage.Proof.Framework.Offset

/-! # The ARMv7 key stages: tools for the stages

`VP.ctx`: a piece the taint analysis checks with the registers of the
working space's context public; `VP.stack`: a piece of loads and stores
relative to the stack. `KS.of_outZ`: memory past the working space changed
(frame word 0). `KR`: a stage but for `r8`, which steps of Montgomery
multiplication's working space keep (`KR.keep`, with `keepM`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

namespace VP
variable {F G : State → State → Prop}

/-- A piece the taint analysis checks with `r7`–`r9` public, at stages of
the working space's context. -/
theorem ctx {P : RP} {c : Prog isa} {v N : Nat}
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs ctxRegs) c hc).isSome = true)
    (hws : ∀ σ s, F σ s → Ws s P.B P.Z v N) (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
    have w₁ := hws _ _ h₁; have w₂ := hws _ _ h₂
    simp only [ctxRegs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · rw [w₁.r7, w₂.r7]
    · rw [w₁.r8, w₂.r8]
    · rw [w₁.r9, w₂.r9]) wp

end VP

section
variable {P : RP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

end

end VG.Proof.Rsa.Arm.Recover
