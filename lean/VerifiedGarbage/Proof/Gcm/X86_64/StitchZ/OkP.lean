import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.LoopP
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Ok
import VerifiedGarbage.Proof.Gcm.Powers

/-!
# The AVX-512 loops with the powers in the key context: both meet their contracts

Untrusted: everything here is checked by Lean. `stitchP_ok`: `StitchZP.enc`
and `StitchZP.dec` meet `StitchOkP`: the setup leaves the state of
`StitchZ.setup_ok` from the powers of the key context (`setupP_ok`): in the
field, `x · (Hⁿ · x⁻¹) = Hⁿ` (`x_φ_hInvF`, `φ_hpow`), so that their products,
and those of the tables loaded (`bigP_ok`, `bigDP_ok`), add up to `GHASH`
(`StitchZ.finZ`, `finZ48`); the rest is `StitchZ`'s (`encTailG_ok`,
`decTailG_ok`).
-/

namespace VG.Proof.Gcm.X86_64.StitchZP

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (SPreP StitchOkP EPost DPost hk)
open VG.Proof.Gcm.X86_64.StitchZ (finZ finZ48 FinOk48 encTailG_ok decTailG_ok)
open VG.Spec.Gcm (Block hpow)

/-- `Hⁿ · x⁻¹`, times `x`, is `Hⁿ`. -/
theorem x_φ_hInvF (H : Block) (n : Nat) : x * φ (hInvF (hpow H n)) = φ H ^ n := by
  rw [hInvF, Pclmul.x_φ_hInv, φ_hpow]

theorem finP {H : Block} {P : Nat → Nat → Block}
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (hpow H (16 - 4 * k - l))) :
    ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ H ^ (16 - 4 * k - l) := fun k hk l hl => by
  rw [hP k hk l hl, x_φ_hInvF]

theorem fin48P (H : Block) (T : Nat → Nat → Nat → Block)
    (hT : ∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (hpow H (48 - 16 * g - 4 * k - l))) : FinOk48 H T :=
  finZ48 fun g hg k hk l hl => by rw [hT g hg k hk l hl, x_φ_hInvF]

/-- The encryption of `n` blocks (a multiple of 16, at least 16). -/
theorem enc_ok {s₀ : State} (hp : SPreP s₀) : WP isa Impl.Gcm.X86_64.StitchZP.enc s₀ (EPost s₀) :=
  WP.seq (WP.mono (setupP_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    encTailG_ok hp.base (finZ (finP hpw))
      (fun _ h256 hI => bigP_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) h256 hI) hR)

/-- The decryption of `n` blocks (a multiple of 16, at least 16). -/
theorem dec_ok {s₀ : State} (hp : SPreP s₀) : WP isa Impl.Gcm.X86_64.StitchZP.dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setupP_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    decTailG_ok hp.base (finZ (finP hpw)) (fun _ h256 hI => bigDP_ok hp hpw (fin48P (hk s₀)) h256 hI) hR)

/-- Both loops meet their contracts. -/
theorem stitchP_ok : StitchOkP Impl.Gcm.X86_64.StitchZP.enc Impl.Gcm.X86_64.StitchZP.dec :=
  ⟨fun _ hp => enc_ok hp, fun _ hp => dec_ok hp⟩

end VG.Proof.Gcm.X86_64.StitchZP
