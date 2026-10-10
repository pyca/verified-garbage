import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsPrologue
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedRestCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsPrologue
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedDepth

/-! ## From `OptimizedPairedCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem pairedSign_correct {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) (σ : State)
    (hpre : (signK p D).pre σ) (hroots : StaticRoots D σ) (rp : PairedRoots D σ) {checks : Prog isa}
    (hinit : 16*(positiveDecodeWith keccak.callee P p).aarch64Depth≤D)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤D)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤D)
    (hchecks : ∀σ s t,PositiveIB p D σ t s → PairedRoots D s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u => (PositiveEP p D σ t u ∨ PositiveEF p D σ t u) ∧ PairedRoots D u) :
    ∃ t s', Exec isa (Impl.MlDsa.AArch64.Sign.Optimized.signWith keccak.callee P p checks) σ t s' ∧ abiPreserved σ s' ∧ (signK p D).post σ s' := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf'
  obtain ⟨hsv, -⟩ := hf'
  have main : WP isa (Impl.MlDsa.AArch64.Sign.Optimized.signWith keccak.callee P p checks) σ fun s₅ => abiPreserved σ s₅ ∧
      ∃ s₄, FS p D σ s₄ ∧ s₅.gpr .x0 = s₄.gpr .x24 ∧ s₅.mem = s₄.mem := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.signWith
    refine WP.seq (WP.mono (paired_prologue h3 hP.s64 hpre hroots rp) fun s₁ ⟨⟨hs,h15⟩,r1⟩ => ?_)
    refine WP.seq (WP.mono (WP.pairedRoots (rooted_expandA_ok hP h3 ha hs h15) r1 (expandA_depth hP p) hP.s64) fun s₂ ⟨⟨h₂,hr₂⟩,r2⟩ => ?_)
    refine WP.seq (WP.mono (show WP isa (ifOk (Impl.MlDsa.AArch64.Sign.Optimized.restWith keccak.callee P p checks)) s₂ (FS p D σ) from ?_) fun s₄ h₄ => ?_)
    · unfold ifOk
      refine ifOkElse_ok (fun hne => ?_) fun he => ?_
      · have h1 := x24_one h₂.r01 hne
        obtain ⟨ok, fam⟩ := h₂.ok h1
        exact pairedRest_ok hP h3 hinit hcommit hball hchecks ⟨h₂.st,ok,fam⟩ hr₂ r2
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

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedConcreteCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem selectedPairedSign_correct (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : Ok3 p) (σ : State) (hpre : (signK p 16).pre σ)
    (hr : StaticRoots 16 σ) (rp : PairedRoots 16 σ) :
    ∃t s',Exec isa (Impl.MlDsa.AArch64.Sign.Optimized.signWith v.callee (primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) σ t s' ∧
      abiPreserved σ s' ∧ (signK p 16).post σ s' := by
  apply pairedSign_correct (keccak:=v) (prims_okWith (keccak:=v)) hp σ hpre hr rp
  · have hd := (Message.pairedInitialization_dle v p).le
    change 16 * _ ≤ 16
    omega
  · have hd := (Message.pairedCommit_dle v hp).le
    change 16 * _ ≤ 16
    omega
  · have hd := (Message.pairedBall_dle v p).le
    change 16 * _ ≤ 16
    omega
  · intro σ s t hi ri h1
    exact positivePairedChecks_ok hp (by rcases hp with rfl|rfl|rfl <;> decide)
      (by decide) (by decide) ri hi h1

end VG.Proof.MlDsa.AArch64.Sign

end
