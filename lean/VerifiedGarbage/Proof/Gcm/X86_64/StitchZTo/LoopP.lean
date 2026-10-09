import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop48
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.LoopP

/-!
# The out-of-place AVX-512 loop, with the powers in the key context

Untrusted: everything here is checked by Lean. `bigPTo_ok`: `StitchZTo.bigPTo`
is `bigRestTo_ok` after `StitchZP.powP48`, which stores the tables of 48
blocks converted from the powers of the key context (`StitchZP.powP48_ok`,
for the in-place view `dst s₀`, whose key context the loop keeps:
`StitchZP.ctx_keep`).
-/

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPreTo CtxMode kp pp nb hk)
open VG.Proof.Gcm.X86_64.StitchZ (FinOk FinOk48)
open VG.Proof.Gcm.X86_64.StitchZP (powP48_ok ctx_keep hInvF)
open VG.Impl.Gcm.X86_64.StitchZ (tab)
open VG.Impl.Gcm.X86_64.StitchZTo (bigPTo)
open VG.Spec.Gcm (Block)

/-- `bigPTo`: `bigTo` with the tables loaded. -/
theorem bigPTo_ok {s₀ : State} (hp : SPreTo CtxMode.powers s₀) (hm : nb s₀ % 16 = 0) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)))
    (hFin : ∀ T : Nat → Nat → Nat → Block,
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow (hk s₀) (48 - 16 * g - 4 * k - l))) →
        FinOk48 (hk s₀) T) (h256 : 256 ≤ nb s₀) {s : State}
    (hI : EInvTo s₀ P 1 s) : WP isa bigPTo s fun s' => ∃ e, EInvTo s₀ P e s' := by
  have hP' := hp.toP
  have hdi : s.gpr .rdi = kp s₀ := hI.gpr .rdi (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hpw, hH⟩ := ctx_keep hP' hI.a.frame
  refine WP.seq (WP.mono (powP48_ok hP' hdi hr11 hI.a.rd hI.a.wr hpw
    (fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact hI.a.msk l (by omega)) hI.m1)
    fun s₁ ⟨t, pm, keep, fr, g₁, rd₁, wr₁, z₁⟩ => ?_)
  rw [hH] at t
  let T : Nat → Nat → Nat → Block := fun g k l =>
    if g = 2 then P k l else s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128
  have hv : ∀ g < 3, ∀ k < 4, ∀ l < 4,
      s₁.mem.readW (pp s₀ + BitVec.ofNat 64 (tab g + 64 * k + 16 * l)) 128 = T g k l := fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2
      simp only [T, ↓reduceIte, show tab 2 + 64 * k + 16 * l = 64 * k + 16 * l by simp only [tab]; omega]
      exact (keep (64 * k + 16 * l) (by omega)).trans (hI.pw k hk l hl)
    · simp only [T, h2, ↓reduceIte]
  have hT : FinOk48 (hk s₀) T := hFin T fun g hg k hk l hl => by
    by_cases h2 : g = 2
    · subst h2; simp only [T, ↓reduceIte]; rw [hP k hk l hl]
    · simp only [T, h2, ↓reduceIte]; exact t g (by omega) k hk l hl
  exact (bigRestTo_ok hp hm hf hT (fun k l => by simp only [T, ↓reduceIte]) h256 hI
    (hI.a.pow hp fr g₁ rd₁ wr₁ fun r h7 h8 h9 h10 _ h12 l hl => z₁ r h7 h8 h9 h10 h12 l hl) hv pm g₁
    fun l hl => z₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl)

end VG.Proof.Gcm.X86_64.StitchZTo
