import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsPrologue
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsPrologue
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem sign_correct {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) (σ : State)
    (hpre : (signK p D).pre σ) (hroots : StaticRoots D σ) (rp : PairedRoots D σ) {checks : Prog isa}
    (hinit : 16*(positiveDecodeWith keccak.callee P p).aarch64Depth≤D)
    (hloop : ∀σ s, PositiveIK p D σ s → PairedRoots D s →
      WP isa (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p checks) s
        (fun u=>PositiveXS p D σ u ∧ PairedRoots D u)) :
    ∃ t s', Exec isa (Impl.MlDsa.AArch64.Sign.Cached.signWith keccak.callee P p checks) σ t s' ∧ abiPreserved σ s' ∧ (signK p D).post σ s' := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf'
  obtain ⟨hsv, -⟩ := hf'
  have main : WP isa (Impl.MlDsa.AArch64.Sign.Cached.signWith keccak.callee P p checks) σ fun s₅ => abiPreserved σ s₅ ∧
      ∃ s₄, FS p D σ s₄ ∧ s₅.gpr .x0 = s₄.gpr .x24 ∧ s₅.mem = s₄.mem := by
    unfold Impl.MlDsa.AArch64.Sign.Cached.signWith
    refine WP.seq (WP.mono (paired_prologue h3 hP.s64 hpre hroots rp) fun s₁ ⟨⟨hs,h15⟩,r1⟩ => ?_)
    refine WP.seq (WP.mono (WP.pairedRoots (CachedMatrix.rooted_expandA_ok hP h3 ha hs h15) r1 (CachedMatrix.expandA_depth hP p) hP.s64) fun s₂ ⟨⟨h₂,hr₂⟩,r2⟩ => ?_)
    refine WP.seq (WP.mono (show WP isa (ifOk (Impl.MlDsa.AArch64.Sign.Cached.restWith keccak.callee P p checks)) s₂ (FS p D σ) from ?_) fun s₄ h₄ => ?_)
    · unfold ifOk
      refine ifOkElse_ok (fun hne => ?_) fun he => ?_
      · have h1 := x24_one h₂.r01 hne
        obtain ⟨ok, fam⟩ := h₂.ok h1
        exact rest_ok hP h3 hinit hloop ⟨h₂.st,ok,fam⟩ hr₂ r2
      · have h0 := x24_zero h₂.r01 he
        exact WP.block_nil ⟨h₂.st, .inl h0, fun h1 => absurd (h1.symm.trans h0) (by decide),
          fun _ => signMu_min_A (h₂.bad h0)⟩
    · exact WP.mono (epi_ok h₄.st.top fun k hk => h₄.st.lay.inR (hsv k hk)) fun s₅ ⟨hg, hr, hm⟩ =>
        ⟨hg, s₄, h₄, hr, hm⟩
  obtain ⟨t, s', he, hF⟩ := main
  obtain ⟨hg, s₄, h₄, hr, hm⟩ := hF
  refine ⟨t, s', he, hg, ?_⟩
  have e23 : pa s₄ (.x23, 0) = σ.gpr .x3 := by
    rw [pa, h₄.st.top.regs (.x23, .x3) (by decide), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  show Outcome _ _ _
  rcases h₄.r01 with h0 | h1
  · exact .inr ⟨by rw [hr, h0]; rfl, h₄.bad h0⟩
  · exact .inl ⟨by rw [hr, h1]; rfl, maxBounds, by rw [hm, ← e23]; exact h₄.ok h1⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached
