module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTable
public import VerifiedGarbage.Proof.MlKem.AArch64.KgB
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPost
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Pair
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset

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

end VG.Proof.MlKem.AArch64.KeyGen
