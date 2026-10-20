module
public import VerifiedGarbage.Proof.MlKem.AArch64.KgB
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTable
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Last

import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPair
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPost
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-! # The odd final matrix entry in key generation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
variable {P : KemLay}

theorem singleton_context {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P s₀ s) (tb : MatrixTable P s₀ s) :
    Paired.SingleContext (kA s₀ 3+BitVec.ofNat 64 SS)
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  have f0 : SS+2048≤kL P 3 := by kl
  have f1 : AH+1024*e+1024≤kL P 3 := matrixEntry_fit hw he
  have ctx : Paired.SingleContext (kA s₀ 3+BitVec.ofNat 64 SS)
      (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
    refine ⟨cov_w hp h (b:=3) (o:=SS) (l:=2048) (by decide) f0,
      cov_w hp h (b:=3) (o:=AH+1024*e) (l:=1024) (by decide) f1,
      hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SS) (l₁:=2048) (o₂:=AH+1024*e) (l₂:=1024)
        (by decide) (by decide) f0 f1 (by lom),tb.artifact,tb.readable,?_,?_⟩
    · exact tb.apart.sub_right (Offset.sub_base (kA s₀ 3) f0)
    · exact tb.apart.sub_right (Offset.sub_base (kA s₀ 3) f1)
  exact ctx

theorem matrix_singleton {w16 : Bool} {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    (h : BInvW w16 P s₀ e s) (tb : MatrixTable P s₀ s) :
    WP isa (Paired.lastCode SB SS e P.k (AH+1024*e) w16) s fun t=>
      BInvW w16 P s₀ (e+1) t ∧ MatrixTable P s₀ t := by
  have hw := hp.wf
  have f0 : SS+2048≤kL P 3 := by kl
  have f1 : AH+1024*e+1024≤kL P 3 := matrixEntry_fit hw he
  have ctx := singleton_context hp he h.kb tb
  refine WP.mono_syms (Paired.lastCode_ok (sb:=SB) (ss:=SS) (a:=e) (k:=P.k) (off:=AH+1024*e)
    (p:=kA s₀ 3+BitVec.ofNat 64 SS) (seed:=kA s₀ 3+BitVec.ofNat 64 SB)
    (out:=kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
    (by decide) (by decide) (by decide) (by lom) (by lom) (by lom)
    (by rw [h.kb.x28]) (by rw [h.kb.x28]) (by rw [h.kb.x28])
    (by
      intro j hj
      rw [ptr_add]
      exact in_R (cov_r hp h.kb (b:=3) (o:=SB) (l:=32) (by decide) (by kl))
        (k:=8*j) (by omega) (by omega))
    (hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=SS) (l₂:=2048)
      (by decide) (by decide) (by kl) f0 (by decide))
    (hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=AH+1024*e) (l₂:=1024)
      (by decide) (by decide) (by kl) f1 (by lom)) ctx rfl
    (by
      rw [h.acc]
      by_cases hh : allOk P s₀ e
      · rw [ite_eq_left hh]; exact Or.inr rfl
      · rw [ite_eq_right hh]; exact Or.inl rfl)) fun t ht sy=>?_
  have out := ht.outcome
  simp only [Paired.seedBytes,h.rho] at out
  exact ⟨h.singleton hp he out,tb.frame out.keep.rd out.keep.wr sy out.frame (last_scratch hp he)⟩

end VG.Proof.MlKem.AArch64.KeyGen
