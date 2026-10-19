module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Top
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
public import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
meta import VerifiedGarbage.Proof.Sha3.AArch64.Callers.Sums
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# The checks of the hashing encapsulation's first phase and tail

For ML-KEM-768 and ML-KEM-1024: the taint analyses of the blocks of `ek`
(`habs768`, `habs1024`) and of the first phase (`startH768_taint`,
`startH1024_taint`), and the stack depth of the tail (`tailH_depth`), for
`Kem16/EncapsFinal.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.FixedHash (fixedHash hole)
open VG.Proof.MlKem

/-! ## The blocks of `ek` -/

theorem absorbWords_erase (r : Reg) (eo n : Nat) :
    Code.eraseOff (.block (Impl.MlKem.AArch64.Hybrid.absorbWords r eo n)) =
      Code.eraseOff (.block (Impl.MlKem.AArch64.Hybrid.absorbWords r 0 n)) := by
  simp only [Code.eraseOff, Impl.MlKem.AArch64.Hybrid.absorbWords, List.map_flatMap, List.map_cons,
    List.map_nil, Instr.eraseOff]

theorem habs_of (S : Impl.MlKem.AArch64.Hybrid.HSrc)
    (hfull : ∃ h, (taint.check (Taint.ofRegs [S.r, .x28])
      (Code.eraseOff (.block (Impl.MlKem.AArch64.Hybrid.absorbWords S.r 0 17))) h).isSome = true)
    (hlast : ∃ h, (taint.check (Taint.ofRegs [S.r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock S (S.len / 136))) h).isSome = true) :
    ∀ blk, 136 * blk < S.len → ∃ h, (taint.check (Taint.ofRegs [S.r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock S blk)) h).isSome = true := by
  intro blk hb
  by_cases hf : 136 * blk + 136 ≤ S.len
  · have e : Impl.MlKem.AArch64.Hybrid.absorbBlock S blk =
        Impl.MlKem.AArch64.Hybrid.absorbWords S.r (S.base + 136 * blk) 17 := by
      simp only [Impl.MlKem.AArch64.Hybrid.absorbBlock, ite_eq_left hf]
    obtain ⟨h, hc⟩ := hfull
    exact ⟨h, by rw [e]; exact Taint.isSome_check_of_eraseOff (absorbWords_erase _ _ _) hc⟩
  · rw [show blk = S.len / 136 by omega]
    exact hlast

theorem habs768 : ∀ blk, 136 * blk < (Impl.MlKem.AArch64.Hybrid.ekSrc lay768).len → ∃ h,
    (taint.check (Taint.ofRegs [(Impl.MlKem.AArch64.Hybrid.ekSrc lay768).r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock (Impl.MlKem.AArch64.Hybrid.ekSrc lay768) blk)) h).isSome = true :=
  habs_of _ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩

theorem habs1024 : ∀ blk, 136 * blk < (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024).len → ∃ h,
    (taint.check (Taint.ofRegs [(Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024).r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024)
        blk)) h).isSome = true :=
  habs_of _ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩

theorem srcOk768 : SrcOk (Impl.MlKem.AArch64.Hybrid.ekSrc lay768) :=
  ⟨.inl rfl, by decide, by decide, by decide⟩

theorem srcOk1024 : SrcOk (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024) :=
  ⟨.inl rfl, by decide, by decide, by decide⟩

/-! ## The rest of the code -/

theorem startH768_taint : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3,.x4])
    (Impl.MlKem.AArch64.Hybrid.startH lay768) h).isSome=true := ⟨_,by taint_decide⟩

theorem startH1024_taint : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3,.x4])
    (Impl.MlKem.AArch64.Hybrid.startH Impl.MlKem1024.AArch64.lay1024) h).isSome=true := ⟨_,by taint_decide⟩

theorem tailH_depth (v : Proof.Sha3.AArch64.Permutation) :
    (Impl.MlKem.AArch64.Hybrid.tailH (fixedHash v.callee)).aarch64Depth ≤ 1 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name) (e := Impl.MlKem.AArch64.Hybrid.tailH (fixedHash hole))
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)

end VG.Proof.MlKem.AArch64.Hybrid
