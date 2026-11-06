module

public import VerifiedGarbage.Proof.MlDsa.ResponseHintContract
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintPacked

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem highBits_small {g : Nat} (hg : IsG g) (r : Zq) :
    0≤highBits g r ∧ highBits g r<44 := by
  rw [VG.Proof.MlDsa.Round.highBits_eq (mem_of_isG hg)]
  rcases hg with rfl | rfl <;>
    simp only [VG.Proof.MlDsa.Round.hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,q] <;> omega

end VG.Proof.MlDsa.AArch64.Optimized.Response
