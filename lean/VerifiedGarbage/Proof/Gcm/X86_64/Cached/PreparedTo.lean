import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Loop48To
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.OutOfPlace

/-! # Prepared tables and the cached-key loop setup -/

namespace VG.Proof.Gcm.X86_64.StitchZHTo
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPreTo CtxMode kp pp hk nr sch nb)
open VG.Proof.Gcm.X86_64.StitchZ (FinOk FinOk48)
open VG.Proof.Gcm.X86_64.StitchZTo (ReadyTo EInvTo AInvTo.pow)
open VG.Proof.Gcm.X86_64.StitchZR (ctx_keep powP48_ok)
open VG.Proof.Gcm.X86_64.StitchZRTo (setupPTo_ok)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF)
open VG.Impl.Gcm.X86_64.StitchZ (tab)
open VG.Impl.Gcm.X86_64.StitchZHTo (bigPTo)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block)

theorem ready_frame {s₀ s t : State} {P : Nat → Nat → Block} (h : ReadyTo s₀ P s)
    (f : ZFrame [] s t) : ReadyTo s₀ P t :=
  ⟨h.a.zframe f (by simp) (by simp) (by simp), by rw [f.gpr]; exact h.rdx,
    by rw [f.gpr]; exact h.rax, fun r h1 h2 h3 h4 => by rw [f.gpr]; exact h.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [f.mem]; exact h.pw k hk l hl,
    fun l hl => by rw [f.zlane _ (by simp) l hl]; exact h.m1 l hl,
    by rw [f.zlane _ (by simp) 0 (by decide)]; exact h.y,
    fun l h1 h4 => by rw [f.zlane _ (by simp) l h4]; exact h.y1 l h1 h4⟩

theorem setup_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) :
    WP isa (.seq (.block Impl.Gcm.X86_64.StitchZRTo.setupP) Impl.Aes.X86_64.VaesZH.loadKeys) s₀ fun s =>
      ∃ P : Nat → Nat → Block, ReadyTo s₀ P s ∧
        (∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l))) ∧
        VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s := by
  refine WP.seq (WP.mono (setupPTo_ok hp) fun s ⟨P, hR, hpw⟩ => ?_)
  refine WP.mono (VG.Proof.Aes.X86_64.VaesZH.loadKeys_ok s (hR.a.keys hp) hp.rounds
    (by rw [hR.a.rsi]; simp)
    (by rw [hR.a.r10, hR.a.rdi])) fun t ⟨hK, hf⟩ => ?_
  exact ⟨P, ready_frame hR hf, hpw, hK⟩

theorem bigPTo_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) {P : Nat → Nat → Block} (hf : FinOk (hk s₀) P)
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)))
    (hFin : ∀ T : Nat → Nat → Nat → Block,
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow (hk s₀) (48 - 16 * g - 4 * k - l))) →
        FinOk48 (hk s₀) T) (h256 : 256 ≤ nb s₀) {s : State}
    (hI : EInvTo s₀ P 1 s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s) : WP isa bigPTo s fun s' => ∃ e, EInvTo s₀ P e s' ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have hP' := hp.toPrepared
  have hdi : s.gpr .rdi = kp s₀ := hI.gpr .rdi (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hpw, hH⟩ := ctx_keep hP' hI.a.frame
  refine WP.seq (WP.mono (WP.hkeep (by decide +kernel) (powP48_ok hP' hdi hr11 hI.a.rd hI.a.wr hpw
    (fun l hl => by rw [← State.zlane_lt2 _ _ hl]; exact hI.a.msk l (by omega)) hI.m1))
    fun s₁ ⟨⟨t, pm, keep, fr, g₁, rd₁, wr₁, z₁⟩, hh₁⟩ => ?_)
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
  have hA₁ := (hI.a.pow hp fr g₁ rd₁ wr₁ fun r h7 h8 h9 h10 _ h12 l hl => z₁ r h7 h8 h9 h10 h12 l hl)
  exact (bigRestTo_ok hp hf hT (fun k l => by simp only [T, ↓reduceIte]) h256 hI
    hA₁ hv pm g₁
    (fun l hl => z₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) l hl)
    (hCache.keep hh₁ (hA₁.keys hp)))

end VG.Proof.Gcm.X86_64.StitchZHTo
