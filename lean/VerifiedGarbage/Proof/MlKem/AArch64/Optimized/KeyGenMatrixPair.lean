module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTable

/-! # Invoke the paired sampler in the existing key-generation workspace -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
variable {P : KemLay}

theorem matrixEntry_fit (hw : P.Wf) {e : Nat} (he : e<P.k*P.k) :
    AH+1024*e+1024≤kL P 3 := by
  have hf := hw.facts
  simp only [AH,kL]
  omega

theorem pair_context {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P s₀ s) (tb : MatrixTable P s₀ s) :
    Paired.Context (kA s₀ 3+BitVec.ofNat 64 SS)
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have tab := tb.artifact
  have tr := tb.readable
  have td := tb.apart
  have hw := hp.wf
  have f0 : SS+2048≤kL P 3 := by kl
  have f1 : AH+1024*e+1024≤kL P 3 := matrixEntry_fit hw (by omega)
  have f2 : AH+1024*(e+1)+1024≤kL P 3 := matrixEntry_fit hw he
  have apart {o l : Nat} (fit : o+l≤P.scl) :
      (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint (R (kA s₀) 3 o l) :=
    td.sub_right (Offset.sub_base (kA s₀ 3) fit)
  have ctx : Paired.Context (kA s₀ 3+BitVec.ofNat 64 SS)
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
    refine ⟨cov_w hp h (b:=3) (o:=SS) (l:=2048) (by decide) f0,cov_w hp h (b:=3) (o:=AH+1024*e) (l:=1024) (by decide) f1,
      cov_w hp h (b:=3) (o:=AH+1024*(e+1)) (l:=1024) (by decide) f2,?_,?_,?_,tab,tr,apart f0,apart f1,apart f2⟩
    · exact hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SS) (l₁:=2048) (o₂:=AH+1024*e) (l₂:=1024) (by decide) (by decide) f0 f1 (by lom)
    · exact hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SS) (l₁:=2048) (o₂:=AH+1024*(e+1)) (l₂:=1024) (by decide) (by decide) f0 f2 (by lom)
    · exact hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=AH+1024*e) (l₁:=1024) (o₂:=AH+1024*(e+1)) (l₂:=1024) (by decide) (by decide) f1 f2 (by omega)
  exact ctx

theorem matrix_pair {w16 : Bool} {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : BInvW w16 P s₀ e s)
    (tb : MatrixTable P s₀ s) :
    WP isa (Impl.MlKem.AArch64.Paired.pair P true e w16) s fun t=>
      BInvW w16 P s₀ (e+2) t ∧ MatrixTable P s₀ t := by
  have hw := hp.wf
  have f0 : SS+2048≤kL P 3 := by kl
  have ctx := pair_context hp he h.kb tb
  rw [Paired.pair_iff]
  refine WP.mono_syms (Paired.pairCode_ok (sb:=SB) (ss:=SS) (a:=e) (b:=e+1) (k:=P.k)
    (oa:=AH+1024*e) (ob:=AH+1024*(e+1))
    (p:=kA s₀ 3+BitVec.ofNat 64 SS) (seed:=kA s₀ 3+BitVec.ofNat 64 SB)
    (outA:=kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
    (outB:=kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))) (by decide) (by decide) (by decide)
    (by lom) (by lom) (by rw [h.kb.x28]) (by rw [h.kb.x28])
    (by rw [h.kb.x28]) (by rw [h.kb.x28])
    (by
      intro j hj
      rw [ptr_add]
      exact in_R (cov_r hp h.kb (b:=3) (o:=SB) (l:=32) (by decide) (by kl))
        (k:=8*j) (by omega) (by omega))
    (hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=SS) (l₂:=2048) (by decide) (by decide) (by kl) f0 (by decide)) ctx rfl
    (by
      rw [h.acc]
      by_cases hh : allOk P s₀ e
      · rw [ite_eq_left hh]; exact Or.inr rfl
      · rw [ite_eq_right hh]; exact Or.inl rfl)) fun t ht sy=>?_
  have out := ht.outcome (by have := hw.facts; omega) (by have := hw.facts; omega)
  simp only [Paired.seedBytes,h.rho] at out
  exact ⟨h.paired hp he out,tb.frame out.keep.rd out.keep.wr sy out.frame (pair_scratch hp he)⟩

end VG.Proof.MlKem.AArch64.KeyGen
