module
public import VerifiedGarbage.Proof.MlKem.AArch64.KgB
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTable
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullPrefix
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Last
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixLast
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPair
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Public-seed timing of the optimized encryption matrix -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
open VG.Proof.MlKem
variable {P : KemLay}

theorem pair_input {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P s₀ s) (tb : MatrixTable P s₀ s) :
    Paired.BeginInput SB SS (AH+1024*e) (AH+1024*(e+1))
      ((kA s₀ 3+BitVec.ofNat 64 SS)) ((kA s₀ 3+BitVec.ofNat 64 SB)) ((kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))) ((kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))))
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨(by rw [h.x28]),(by rw [h.x28]),(by rw [h.x28]),(by rw [h.x28]),?_,
    hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=SS) (l₂:=2048) (by decide) (by decide) (by kl) (by kl) (by decide),pair_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_r hp h (b:=3) (o:=SB) (l:=32) (by decide) (by kl)) (k:=8*j) (by omega) (by omega)

theorem last_input {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P s₀ s) (tb : MatrixTable P s₀ s) :
    Paired.LastInput SB SS (AH+1024*e) ((kA s₀ 3+BitVec.ofNat 64 SS)) ((kA s₀ 3+BitVec.ofNat 64 SB)) ((kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)))
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨(by rw [h.x28]),(by rw [h.x28]),(by rw [h.x28]),?_,
    hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=SS) (l₂:=2048) (by decide) (by decide) (by kl) (by kl) (by decide),singleton_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_r hp h (b:=3) (o:=SB) (l:=32) (by decide) (by kl)) (k:=8*j) (by omega) (by omega)

end VG.Proof.MlKem.AArch64.KeyGen
