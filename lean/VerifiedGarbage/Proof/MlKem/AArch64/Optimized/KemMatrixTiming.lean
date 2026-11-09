module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullPrefix
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Public-seed timing of the optimized encryption matrix -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Spec.MlKem
open VG.Proof.MlKem
variable {P : KemLay} {L : Layout}

theorem pair_input {s₀ s : State} (hp : Pre P L s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P L s₀ s) (tb : MatrixTable P L s₀ s) :
    Paired.BeginInput SB SS (AH+1024*e) (AH+1024*(e+1))
      (sA L s₀ SS) (sA L s₀ SB) (aP L s₀ e) (aP L s₀ (e+1))
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨e28 h SS,e28 h SB,e28 h _,e28 h _,?_,
    sdisj hp (by lom) (by lom) (by decide),pair_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_sr hp h (o:=SB) (l:=32) (by lom)) (k:=8*j) (by omega) (by omega)

theorem last_input {s₀ s : State} (hp : Pre P L s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P L s₀ s) (tb : MatrixTable P L s₀ s) :
    Paired.LastInput SB SS (AH+1024*e) (sA L s₀ SS) (sA L s₀ SB) (aP L s₀ e)
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨e28 h SS,e28 h SB,e28 h _,?_,
    sdisj hp (by lom) (by lom) (by decide),singleton_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_sr hp h (o:=SB) (l:=32) (by lom)) (k:=8*j) (by omega) (by omega)

end VG.Proof.MlKem.AArch64.Kem
