import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Load
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.SetupP

/-! # Preparing the AVX-512 loop state by loading encoded powers -/

namespace VG.Proof.Gcm.X86_64.StitchZR
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPrePrepared kp hk in_sub_int setupT_ok)
open VG.Proof.Gcm.X86_64.Pclmul (const_ok)
open VG.Impl.Gcm.X86_64.Pclmul (poly revMask)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZR (cvtPair setupGP setupP)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF vinsSelf_ok cvtRegs preg16_mem preg16_inj)

/-- Load the first `n` register pairs from the prepared context. -/
theorem cvtRun_ok {s₀ : State} (hp : SPrePrepared s₀) :
    ∀ n, n ≤ 8 → ∀ s, s.gpr .rdi = kp s₀ → s.mem = s₀.mem → s.rd = s₀.rd → s.wr = s₀.wr →
      WP isa (.block ((List.range n).flatMap fun k => cvtPair (15 - 2*k) (preg16 k))) s fun s' =>
        (∀ k < n, ∀ l < 2, s'.lane (preg16 k) l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2*k - l))) ∧
        YFrame cvtRegs s s'
  | 0, _, s, _, _, _, _ => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨fun k hk => absurd hk (by omega), YFrame.refl _ _⟩
  | n+1, hn, s, hdi, hm, hrd, hwr => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (cvtRun_ok hp n (by omega) s hdi hm hrd hwr) fun s₁ ⟨p₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hin : InRegions (s₁.rd ++ s₁.wr)
        (s₁.gpr .rdi + BitVec.ofInt 64 ((240 + 16*(15-2*n) : Nat) : Int)) 32 := by
      rw [f₁.rd, f₁.wr, f₁.gpr, hrd, hwr, hdi]
      exact in_sub_int hp.k_in (by omega)
    refine WP.mono (loadPair_ok (15-2*n) (preg16 n) s₁ hin) fun s' ⟨v, z⟩ => ?_
    have f := z.yframe
    refine ⟨fun k hk l hl => ?_, f₁.trans (f.mono fun r hr => ?_)⟩
    · by_cases hkn : k = n
      · subst k
        rw [v l hl, f₁.mem, hm, f₁.gpr, hdi,
          pair_values hp.pow (by omega) (by omega) hl]
        congr 2; omega
      · rw [f.lane _ (fun h => hkn (preg16_inj k (by omega) n (by omega) (List.mem_singleton.mp h))) l hl]
        exact p₁ k (by omega) l hl
    · have e := List.mem_singleton.mp hr
      subst r
      exact preg16_mem n

/-- `setupGP`: what `Stitch.setupG_ok` says of `setupG`. -/
theorem setupGP_ok {s₀ : State} (hp : SPrePrepared s₀) :
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
  refine WP.mono (cvtRun_ok hp 8 (Nat.le_refl _) s₄ (g₄ _ (by decide)) mm₄ rd₄ wr₄)
    fun s' ⟨pw, F⟩ =>
    ⟨fun l hl => by rw [F.lane _ (by decide) l hl]; exact m0 l hl,
      fun l hl => by rw [F.lane _ (by decide) l hl]; exact m1 l hl, pw,
      fun r hr => by rw [F.gpr, g₄ r hr], by rw [F.mem, mm₄], by rw [F.rd, rd₄], by rw [F.wr, wr₄]⟩

/-- `setupP`: the state the AVX-512 loops start from, with the powers
`Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ · x⁻¹` in the working space, as `StitchZ.setup_ok`. -/
theorem setupP_ok {s₀ : State} (hp : SPrePrepared s₀) :
    WP isa (.block setupP) s₀ fun s => ∃ P, StitchZ.Ready s₀ P s ∧
      ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)) := by
  rw [setupP, List.append_assoc, List.append_assoc, WP.block_append_iff, ← List.append_assoc]
  refine WP.mono (setupGP_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (setupT_ok hp.base l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => WP.mono (StitchZ.setupZ_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega]
      exact pw _ (by omega) _ (by omega)⟩

end VG.Proof.Gcm.X86_64.StitchZR
