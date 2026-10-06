import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecP

/-!
# The setup of the AVX-512 loops, from the powers in the key context

Untrusted: everything here is checked by Lean. `setupGP_ok`: `StitchZP.setupGP`
leaves what `Stitch.setupG` does (`Stitch.setupG_ok`): the constants in both
lanes of `ymm0` and `ymm1`, and in the lanes of `ymm3`–`ymm6`,
`ymm12`–`ymm15` the powers `H¹⁶⁻²ᵏ⁻ˡ · x⁻¹` (`hInvF`), each converted from
the power the key context holds (`cvtPair_ok`, `Spec.Gcm.PowersRepr`).
`setupP_ok`: then `StitchZ`'s rest of the setup (`Stitch.setupT_ok`,
`setupZ_ok`), as `StitchZ.setup_ok`, the field aside (`StitchZ/OkP.lean`).
-/

namespace VG.Proof.Gcm.X86_64.StitchZP

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreP kp hk in_sub_int setupT_ok)
open VG.Proof.Gcm.X86_64.Pclmul (Only const_ok)
open VG.Impl.Gcm.X86_64.Pclmul (at_ xInv poly revMask)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZP (cvtConsts cvtPair setupGP setupP)

/-- `vinserti128 r, r, r, 1`: lane 0 copied to lane 1. -/
theorem vinsSelf_ok (r : XReg) (s : State) :
    WP isa (.block [.vop (.vinserti128 r r r 1)]) s fun s' =>
      (∀ l < 2, s'.lane r l = s.lane r 0) ∧ YFrame [r] s s' := by
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨fun l hl => ?_, rfl, rfl, rfl, rfl, fun r' hr l hl => ?_⟩⟩
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [VOp.exec, State.setV, State.lane]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [hr, VOp.exec, State.setV, State.lane]

theorem preg16_ne (k : Nat) : preg16 k ≠ .xmm0 ∧ preg16 k ≠ .xmm1 ∧ preg16 k ≠ .xmm7 ∧ preg16 k ≠ .xmm8 ∧
    preg16 k ≠ .xmm9 ∧ preg16 k ≠ .xmm10 := by
  unfold preg16; split <;> decide

theorem preg16_inj : ∀ k < 8, ∀ k' < 8, preg16 k = preg16 k' → k = k' := by decide

/-- The registers the conversions write. -/
abbrev cvtRegs : List XReg := [.xmm7, .xmm10, .xmm3, .xmm4, .xmm5, .xmm6, .xmm15, .xmm14, .xmm13, .xmm12]

theorem preg16_mem (k : Nat) : preg16 k ∈ cvtRegs := by unfold preg16; split <;> decide

/-- The block of the key context at `256 + 16 k`, for `k < 48`, is `Hᵏ⁺¹`. -/
theorem pow_at {s₀ : State} (hp : SPreP s₀) {k : Nat} (hk48 : k < 48) :
    Spec.Gcm.blockAt s₀.mem (kp s₀ + BitVec.ofInt 64 ((256 + 16 * k : Nat) : Int)) = Spec.Gcm.hpow (hk s₀) (k + 1) := by
  rw [BitVec.ofInt_natCast, hp.pow k hk48]; rfl

/-- The pairs `0 … n - 1`. -/
theorem cvtRun_ok {s₀ : State} (hp : SPreP s₀) :
    ∀ n, n ≤ 8 → ∀ s, s.gpr .rdi = kp s₀ → s.mem = s₀.mem → s.rd = s₀.rd → s.wr = s₀.wr →
      (∀ l < 2, s.lane .xmm0 l = revMask) → (∀ l < 2, s.lane .xmm8 l = xInv) →
      (∀ l < 2, s.lane .xmm9 l = ones) →
      WP isa (.block ((List.range n).flatMap fun k => cvtPair (15 - 2 * k) (preg16 k))) s fun s' =>
        (∀ k < n, ∀ l < 2, s'.lane (preg16 k) l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * k - l))) ∧ YFrame cvtRegs s s'
  | 0, _, s, _, _, _, _, _, _, _ => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨fun k hk => absurd hk (by omega), YFrame.refl _ _⟩
  | n + 1, hn, s, hdi, hm, hrd, hwr, h0, h8, h9 => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (cvtRun_ok hp n (by omega) s hdi hm hrd hwr h0 h8 h9) fun s₁ ⟨p₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain ⟨_, _, n7, n8, n9, n10⟩ := preg16_ne n
    have kin : ∀ o : Nat, o + 16 ≤ 1024 → InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofInt 64 (o : Int)) 16 :=
      fun o ho => by rw [f₁.rd, f₁.wr, f₁.gpr, hrd, hwr, hdi]; exact in_sub_int hp.k_in ho
    refine WP.mono (cvtPair_ok (15 - 2 * n) (preg16 n) n7 n8 n9 n10 s₁
      (fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact h0 l hl)
      (fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact h8 l hl)
      (fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact h9 l hl)
      (kin _ (by omega)) (kin _ (by omega))) fun s' ⟨v0, v1, f'⟩ => ⟨fun k hk l hl => ?_, ?_⟩
    · rw [f₁.mem, f₁.gpr, hm, hdi] at v0 v1
      by_cases hkn : k = n
      · subst hkn
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · rw [v0, pow_at hp (by omega)]; congr 2; omega
        · rw [v1, show 240 + 16 * (15 - 2 * k) = 256 + 16 * (14 - 2 * k) by omega, pow_at hp (by omega)]
          congr 2; omega
      · rw [f'.lane _ (fun h => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h | h
          · exact (preg16_ne k).2.2.1 h
          · exact (preg16_ne k).2.2.2.2.2 h
          · exact hkn (preg16_inj k (by omega) n (by omega) h)) l hl]
        exact p₁ k (by omega) l hl
    · refine ⟨f'.gpr.trans f₁.gpr, f'.mem.trans f₁.mem, f'.rd.trans f₁.rd, f'.wr.trans f₁.wr, fun r hr l hl => ?_⟩
      rw [f'.lane r (fun h => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · decide
        · decide
        · exact preg16_mem n)) l hl, f₁.lane r hr l hl]

/-- `setupGP`: what `Stitch.setupG_ok` says of `setupG`. -/
theorem setupGP_ok {s₀ : State} (hp : SPreP s₀) :
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
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₄ m1) fun s₅ ⟨c8, c9, f₅⟩ => ?_
  have g₅ : ∀ r, r ≠ .rax → s₅.gpr r = s₀.gpr r := fun r hr => by rw [f₅.gpr, f₄.gpr, f₃.gpr, o₁₂.gpr r hr]
  have mm₅ : s₅.mem = s₀.mem := by rw [f₅.mem, f₄.mem, f₃.mem, o₁₂.mem]
  have rd₅ : s₅.rd = s₀.rd := by rw [f₅.rd, f₄.rd, f₃.rd, o₁₂.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [f₅.wr, f₄.wr, f₃.wr, o₁₂.wr]
  refine WP.mono (cvtRun_ok hp 8 (Nat.le_refl _) s₅ (g₅ _ (by decide)) mm₅ rd₅ wr₅
    (fun l hl => by rw [f₅.lane _ (by decide) l hl]; exact m0 l hl) c8 c9) fun s' ⟨pw, F⟩ =>
    ⟨fun l hl => by rw [F.lane _ (by decide) l hl, f₅.lane _ (by decide) l hl]; exact m0 l hl,
      fun l hl => by rw [F.lane _ (by decide) l hl, f₅.lane _ (by decide) l hl]; exact m1 l hl, pw,
      fun r hr => by rw [F.gpr, g₅ r hr], by rw [F.mem, mm₅], by rw [F.rd, rd₅], by rw [F.wr, wr₅]⟩

/-- `setupP`: the state the AVX-512 loops start from, with the powers
`Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ · x⁻¹` in the working space, as `StitchZ.setup_ok`. -/
theorem setupP_ok {s₀ : State} (hp : SPreP s₀) :
    WP isa (.block setupP) s₀ fun s => ∃ P, StitchZ.Ready s₀ P s ∧
      ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)) := by
  rw [setupP, List.append_assoc, List.append_assoc, WP.block_append_iff, ← List.append_assoc]
  refine WP.mono (setupGP_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (setupT_ok hp.base l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => WP.mono (StitchZ.setupZ_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega]
      exact pw _ (by omega) _ (by omega)⟩

end VG.Proof.Gcm.X86_64.StitchZP
