module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context

/-! # The 512-bit loops over a source, without the field

Untrusted: everything here is checked by Lean. What `StitchZHTo.phase1`
leaves, with the powers the setup stores stated by the products they give
(`StitchZ.FinOk`) rather than in the field: proved where that algebra is
imported (`StitchZHTo.phase1_ok`, `StitchZ/OkP.lean`) and passed to the
proofs of `StitchZHTo.encN` (`Cached/OnePass.lean`), which so need not import
it. -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPreTo CtxMode nb nr sch hk)

/-- What `phase1` leaves: the out-of-place loops' invariant after their last
group `e` (`nb = 16 e`), the round keys in registers, and the powers' products. -/
def PhaseOne : Prop :=
  ∀ {s₀ : State}, SPreTo CtxMode.prepared s₀ → nb s₀ % 16 = 0 →
    WP isa Impl.Gcm.X86_64.StitchZHTo.phase1 s₀ fun s => ∃ P e, nb s₀ = 16 * e ∧
      StitchZTo.EInvTo s₀ P e s ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s ∧ StitchZ.FinOk (hk s₀) P

end VG.Proof.Gcm.X86_64.StitchZHTo
