module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Setup
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.OutOfPlace
public import VerifiedGarbage.Proof.Gcm.Powers
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The 256-bit interleaved loops with prepared powers meet their contracts

Untrusted: everything here is checked by Lean. `StitchR.setup` loads the
pairs of powers as `StitchZR.setupGP_ok` says, which `Stitch.setupG_ok`'s
postcondition is, with `x · H'ⁿ = Hⁿ` for `H'ⁿ = Hⁿ · x⁻¹` (`x_φ_hInvF`);
the rest of the setup and the loops are `Stitch`'s (`setupT_ok`,
`encTail_ok`, `decTail_ok`), and out of place `StitchTo`'s.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (nb SPre SPreM SPreTo SPrePrepared StitchOkM StitchToOkM CtxMode EPost DPost
  EPostTo hk Ready setupT_ok encTail_ok decTail_ok finE finD)
open VG.Proof.Gcm.X86_64.StitchTo (ReadyTo encTailTo_ok)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF)
open VG.Spec.Gcm (Block hpow)

/-- `Hⁿ · x⁻¹`, times `x`, is `Hⁿ`. -/
theorem x_φ_hInvF (H : Block) (n : Nat) : x * φ (hInvF (hpow H n)) = φ H ^ n := by
  rw [hInvF, Pclmul.x_φ_hInv, φ_hpow]

/-- The setup: the state the loops start from, as `Stitch.setup_ok`. -/
theorem setup_ok {s₀ : State} (hp : SPrePrepared s₀) :
    WP isa (.block Impl.Gcm.X86_64.StitchR.setup) s₀ fun s => ∃ P, Ready s₀ P s ∧
      ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := by
  simp only [Impl.Gcm.X86_64.StitchR.setup, List.append_assoc]
  rw [WP.block_append_iff]
  exact WP.mono (StitchZR.setupGP_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ =>
    WP.mono (setupT_ok hp.base l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR =>
      ⟨_, hR, fun k hk l hl => by rw [pw k hk l hl]; exact x_φ_hInvF _ _⟩

theorem enc_ok {s₀ : State} (hp : SPrePrepared s₀) (hm : nb s₀ % 16 = 0) :
    WP isa Impl.Gcm.X86_64.StitchR.enc s₀ (EPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw⟩ => encTail_ok hp.base hm (finE hpw) hR)

theorem dec_ok {s₀ : State} (hp : SPrePrepared s₀) (hm : nb s₀ % 16 = 0) :
    WP isa Impl.Gcm.X86_64.StitchR.dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw⟩ => decTail_ok hp.base hm (finD hpw) hR)

/-- Both in-place loops, for a prepared key context. -/
theorem stitch_ok : StitchOkM CtxMode.prepared Impl.Gcm.X86_64.StitchR.enc Impl.Gcm.X86_64.StitchR.dec :=
  ⟨fun _ hp hm => enc_ok hp.toPrepared hm, fun _ hp hm => dec_ok hp.toPrepared hm⟩

/-- The out-of-place setup, as `StitchTo.setupTo_ok`. -/
theorem setupTo_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) :
    WP isa (.block Impl.Gcm.X86_64.StitchR.setupTo) s₀ fun s => ∃ P, ReadyTo s₀ P s ∧
      ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := by
  rw [Impl.Gcm.X86_64.StitchR.setupTo, List.append_assoc, WP.block_append_iff]
  refine WP.mono (StitchZRTo.setupGPTo_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  exact WP.mono (StitchZTo.setupTTo_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR =>
    ⟨_, ReadyTo.ofReady2 hR, fun k hk l hl => by rw [pw k hk l hl]; exact x_φ_hInvF _ _⟩

/-- The out-of-place loop, for a prepared key context. -/
theorem stitchTo_ok : StitchToOkM CtxMode.prepared Impl.Gcm.X86_64.StitchR.encTo := fun _ hp hm =>
  WP.seq (WP.mono (setupTo_ok hp) fun _ ⟨_, hR, hpw⟩ => encTailTo_ok hp hm (finE hpw) hR)

end VG.Proof.Gcm.X86_64.StitchR
