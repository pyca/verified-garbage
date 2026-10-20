module
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole

import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
import VerifiedGarbage.Proof.Framework.KernelRfl
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
meta import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import Mathlib.Tactic.NormNum.Pow
meta import Mathlib.Tactic.NormNum.OfScientific
meta import Mathlib.Tactic.NormNum.DivMod
meta import Mathlib.Tactic.NormNum.Abs
meta import Mathlib.Data.Rat.Cast.Order
meta import VerifiedGarbage.Proof.Sha3.AArch64.Variant
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbols
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbols

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

theorem startH1024_taint : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3,.x4])
    (Impl.MlKem.AArch64.Hybrid.startH Impl.MlKem1024.AArch64.lay1024) h).isSome=true := ⟨_,by taint_decide⟩

theorem tailH_depth (v : Proof.Sha3.AArch64.Permutation) :
    (Impl.MlKem.AArch64.Hybrid.tailH (fixedHash v.callee)).aarch64Depth ≤ 1 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name) (e := Impl.MlKem.AArch64.Hybrid.tailH (fixedHash hole))
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)

end VG.Proof.MlKem.AArch64.Hybrid
