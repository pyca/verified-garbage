module
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyPre

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
import VerifiedGarbage.Proof.MlKem.Mem

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_movz)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem cachedSaves_vals {p : Params} {s s1 : State} (o : Only [.x9] s s1) :
    ∀ j (hj : j < cachedVerifySaves.length), s1.gpr (cachedVerifySaves[j]'hj).1 = (cachedLay p s).vals.getD j 0 := by
  intro j hj
  have : j < 8 := hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [cachedVerifySaves, Lay.vals, cachedLay, List.getElem_cons_zero, List.getElem_cons_succ, List.getD_cons_zero,
      List.getD_cons_succ] <;> exact o.get _

end VG.Proof.MlDsa.AArch64.Optimized.CachedVerify
