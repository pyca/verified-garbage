import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.LoopP

/-! # Prepared GHASH contexts for out-of-place encryption -/

namespace VG.Proof.Gcm.X86_64.Stitch
open VG VG.X86_64
/-- The in-place view used by the shared table-loader proofs. -/
theorem SPreTo.toPrepared {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) :
    SPrePrepared (StitchZTo.dst s₀) :=
  ⟨hp.toD, hp.k_in, hp.wrap_k, hp.k_o.symm, hp.k_p.symm, hp.ok⟩
end VG.Proof.Gcm.X86_64.Stitch

namespace VG.Proof.Gcm.X86_64.StitchZRTo
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPreTo CtxMode kp pp nb hk)
open VG.Proof.Gcm.X86_64.StitchZ (FinOk FinOk48)
open VG.Proof.Gcm.X86_64.StitchZR (powP48_ok ctx_keep cvtRun_ok)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF vinsSelf_ok)
open VG.Proof.Gcm.X86_64.Pclmul (const_ok)
open VG.Impl.Gcm.X86_64.Pclmul (poly revMask)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZ (tab)
open VG.Impl.Gcm.X86_64.StitchZR (setupGP)
open VG.Impl.Gcm.X86_64.StitchZRTo (setupP bigPTo)
open VG.Proof.Gcm.X86_64.StitchZTo (EInvTo ReadyTo setupTTo_ok setupZTo_ok bigRestTo_ok)
open VG.Spec.Gcm (Block)

/-- `setupGP`: what `Stitch.setupG_ok` says of `setupG`. -/
theorem setupGPTo_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) :
    WP isa (.block setupGP) s₀ fun s =>
      (∀ l < 2, s.lane .xmm0 l = revMask) ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
      (∀ k < 8, ∀ l < 2, s.lane (preg16 k) l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * k - l))) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  simp only [setupGP, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff, show ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] :
    List Instr) = [.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1)] ++ [.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] from rfl,
    WP.block_append_iff]
  refine WP.mono (vinsSelf_ok .xmm0 s₂) fun s₃ ⟨v₃, f₃⟩ => ?_
  refine WP.mono (vinsSelf_ok .xmm1 s₃) fun s₄ ⟨v₄, f₄⟩ => ?_
  have m0 : ∀ l < 2, s₄.lane .xmm0 l = revMask := fun l hl => by
    rw [f₄.lane _ (by decide) l hl, v₃ l hl]; show s₂.xmm .xmm0 = _; rw [o₂.xmm _ (by decide), c₁]; rfl
  have m1 : ∀ l < 2, s₄.lane .xmm1 l = poly := fun l hl => by
    rw [v₄ l hl, f₃.lane _ (by decide) 0 (by decide)]; exact c₂
  have g₄ : ∀ r, r ≠ .rax → s₄.gpr r = s₀.gpr r := fun r hr => by rw [f₄.gpr, f₃.gpr, o₁₂.gpr r hr]
  have mm₄ : s₄.mem = s₀.mem := by rw [f₄.mem, f₃.mem, o₁₂.mem]
  have rd₄ : s₄.rd = s₀.rd := by rw [f₄.rd, f₃.rd, o₁₂.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [f₄.wr, f₃.wr, o₁₂.wr]
  refine WP.mono (cvtRun_ok hp.toPrepared 8 (Nat.le_refl _) s₄ (g₄ _ (by decide)) mm₄ rd₄ wr₄)
    fun s' ⟨pw, F⟩ =>
    ⟨fun l hl => by rw [F.lane _ (by decide) l hl]; exact m0 l hl,
      fun l hl => by rw [F.lane _ (by decide) l hl]; exact m1 l hl, pw,
      fun r hr => by rw [F.gpr, g₄ r hr], by rw [F.mem, mm₄], by rw [F.rd, rd₄], by rw [F.wr, wr₄]⟩

/-- The setup: the state the loop starts from, with the powers
`Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ · x⁻¹` in the working space. -/
theorem setupPTo_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) :
    WP isa (.block setupP) s₀ fun s => ∃ P, ReadyTo s₀ P s ∧
      ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)) := by
  rw [setupP, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setupGPTo_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  exact WP.mono (setupTTo_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => WP.mono (setupZTo_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega]
      exact pw _ (by omega) _ (by omega)⟩

/-- `bigPTo`: `bigTo` with the tables loaded. -/
theorem bigPTo_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)))
    (hFin : ∀ T : Nat → Nat → Nat → Block,
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow (hk s₀) (48 - 16 * g - 4 * k - l))) →
        FinOk48 (hk s₀) T) (h256 : 256 ≤ nb s₀) {s : State}
    (hI : EInvTo s₀ P 1 s) : WP isa bigPTo s fun s' => ∃ e, EInvTo s₀ P e s' := by
  have hP' := hp.toPrepared
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
  exact (bigRestTo_ok hp hf hT (fun k l => by simp only [T, ↓reduceIte]) h256 hI
    (hI.a.pow hp fr g₁ rd₁ wr₁ fun r h7 h8 h9 h10 _ h12 l hl => z₁ r h7 h8 h9 h10 h12 l hl) hv pm g₁
    fun l hl => z₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl)

end VG.Proof.Gcm.X86_64.StitchZRTo
