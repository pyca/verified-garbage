module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Loop
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context

/-! # The 256-bit loop's out-of-place setup, without the field

Untrusted: everything here is checked by Lean. What `StitchR.setupTo`
leaves, with the powers it stores stated by the products they give
(`Stitch.FinOk`) rather than in the field (`StitchR.setupTo_ok`): proved
where that algebra is imported (`setupFin`, `StitchR/Ok.lean`) and passed to
the proofs of the one-pass loop (`OnePass.lean`), which so need not import
it. -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPreTo CtxMode hk)
open VG.Proof.Gcm.X86_64.StitchTo (ReadyTo)

/-- `setupTo` leaves the powers of the key context ready, and their products
those of an encryption body. -/
def SetupFin (np : Nat := 24) (hn : 8 ≤ np ∧ np ≤ 24 := by decide) : Prop :=
  ∀ {s₀ : State}, SPreTo (CtxMode.preparedN np hn) s₀ →
    WP isa (.block Impl.Gcm.X86_64.StitchR.setupTo) s₀ fun s => ∃ P, ReadyTo s₀ P s ∧
      Stitch.FinOk Impl.Gcm.X86_64.Stitch.ordE (hk s₀) P

end VG.Proof.Gcm.X86_64.StitchR
