module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Top
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.EncapsVerified
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.EncapsChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# `vg_mlkem768_encaps_sha3` and `vg_mlkem1024_encaps_sha3`, hashing `ek` in the matrix

The instances of `using_correctH` and `encapsH_ct` for ML-KEM-768 and
ML-KEM-1024, with the taint analyses of the code decided on each, and their
contract: `Spec.MlKem.encapsContract` with the constant tables and 128
bytes of stack (`encapsH768_verified`, `encapsH1024_verified`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.FixedHash (fixedHash prf prf_valid)
open VG.Proof.MlKem

/-! ## The blocks of `ek` -/

theorem absorbWords_erase (eo n : Nat) :
    Code.eraseOff (.block (Impl.MlKem.AArch64.Hybrid.absorbWords eo n)) =
      Code.eraseOff (.block (Impl.MlKem.AArch64.Hybrid.absorbWords 0 n)) := by
  simp only [Code.eraseOff, Impl.MlKem.AArch64.Hybrid.absorbWords, List.map_flatMap, List.map_cons,
    List.map_nil, Instr.eraseOff]

theorem absorbFull_taint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x28])
    (Code.eraseOff (.block (Impl.MlKem.AArch64.Hybrid.absorbWords 0 17))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem habs_of (L : KemLay)
    (hlast : ∃ h, (taint.check (Taint.ofRegs [.x25, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock L (L.ekLen / 136))) h).isSome = true) :
    ∀ blk, 136 * blk < L.ekLen → ∃ h, (taint.check (Taint.ofRegs [.x25, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock L blk)) h).isSome = true := by
  intro blk hb
  by_cases hf : 136 * blk + 136 ≤ L.ekLen
  · have e : Impl.MlKem.AArch64.Hybrid.absorbBlock L blk = Impl.MlKem.AArch64.Hybrid.absorbWords (136 * blk) 17 := by
      simp only [Impl.MlKem.AArch64.Hybrid.absorbBlock, ite_eq_left hf]
    obtain ⟨h, hc⟩ := absorbFull_taint
    exact ⟨h, by rw [e]; exact Taint.isSome_check_of_eraseOff (absorbWords_erase _ _) hc⟩
  · rw [show blk = L.ekLen / 136 by omega]
    exact hlast

theorem habs768 : ∀ blk, 136 * blk < lay768.ekLen → ∃ h, (taint.check (Taint.ofRegs [.x25, .x28])
    (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock lay768 blk)) h).isSome = true :=
  habs_of lay768 ⟨_, by taint_decide⟩

theorem habs1024 : ∀ blk, 136 * blk < Impl.MlKem1024.AArch64.lay1024.ekLen → ∃ h,
    (taint.check (Taint.ofRegs [.x25, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock Impl.MlKem1024.AArch64.lay1024 blk)) h).isSome = true :=
  habs_of Impl.MlKem1024.AArch64.lay1024 ⟨_, by taint_decide⟩

/-! ## The rest of the code -/

theorem startH768_taint : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3,.x4])
    (Impl.MlKem.AArch64.Hybrid.startH lay768) h).isSome=true := ⟨_,by taint_decide⟩

theorem restH768_taint : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
    (.seq (Impl.MlKem.AArch64.Hybrid.tailH fixedHash) (Impl.MlKem.AArch64.Optimized.enRestUsing prf lay768)) h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem startH1024_taint : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3,.x4])
    (Impl.MlKem.AArch64.Hybrid.startH Impl.MlKem1024.AArch64.lay1024) h).isSome=true := ⟨_,by taint_decide⟩

theorem restH1024_taint : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
    (.seq (Impl.MlKem.AArch64.Hybrid.tailH fixedHash)
      (Impl.MlKem.AArch64.Optimized.enRestUsing prf Impl.MlKem1024.AArch64.lay1024)) h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem matrixH768_depth : (Impl.MlKem.AArch64.Hybrid.matrixH lay768).aarch64Depth ≤ 8 := by decide +kernel
theorem matrixH1024_depth : (Impl.MlKem.AArch64.Hybrid.matrixH Impl.MlKem1024.AArch64.lay1024).aarch64Depth ≤ 8 := by
  decide +kernel
theorem tailH_depth : (Impl.MlKem.AArch64.Hybrid.tailH fixedHash).aarch64Depth ≤ 1 := by decide +kernel

end VG.Proof.MlKem.AArch64.Hybrid
