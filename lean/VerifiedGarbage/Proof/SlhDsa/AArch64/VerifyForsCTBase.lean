module

-- separate module: the taint checks of `forsPk`'s blocks, rebuilt only when its blocks change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsGroup
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTBase
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsGroup
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTBase

/-!
# SLH-DSA (SHAKE) on AArch64: `forsPk` is constant time, its blocks

The taint analysis checks each block of `forsPk` (`Impl/SlhDsa/AArch64/Verify.lean`)
from the stack pointer and the registers both runs agree on, for each of
the six parameter sets (`Fors.As`): `x19` (`scratch`), `x20` (`kp`), `x21`
(`sig`), `x22` (the group's first tree), `x23` (the height) and the lanes'
indices `x24`–`x27`, all public in verification. The lanes' indices are
loaded from memory, which the analysis treats as secret: the proofs of the
blocks that branch on them start from their values (`VerifyForsCT.lean`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.ForsPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.AArch64 (Layout thashArgs)
open VG.Proof.SlhDsa.AArch64.TreeBase (taintR)
open VG.Proof.SlhDsa.AArch64.Fors (Agree As)

section
variable {P : State → State → Prop}

theorem ct_x23 (hr : Agree P []) : RelCT isa P (.block [.movz .x .x23 0 0]) fun _ _ => True :=
  taintR _ hr (by taint_decide)

theorem ct_frestore (hr : Agree P [.x19]) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.restoreRegs 2 Impl.SlhDsa.AArch64.Verify.fsaved)) fun _ _ => True :=
  taintR _ hr (by taint_decide)

variable {p : Params} (hA : As p)
include hA

/-- The prologue and the indices. -/
theorem ct_fentry (hr : Agree P [.x0]) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.Verify.fpro ++ Impl.SlhDsa.AArch64.Fors.indices p.a p.k ++
      ([.movz .x .x22 0 0] : List Instr))) fun _ _ => True := by
  rcases hA with ⟨-, ha, hk⟩ | ⟨-, ha, hk⟩ | ⟨-, ha, hk⟩ | ⟨-, ha, hk⟩ | ⟨-, ha, hk⟩ | ⟨-, ha, hk⟩ <;>
    simp only [ha, hk] <;> exact taintR _ hr (by taint_decide)

/-- The leaves' block. -/
theorem ct_leaves (hr : Agree P [.x19, .x20, .x21, .x22]) :
    RelCT isa P (.block ((List.range 4).flatMap (leafL p))) fun _ _ => True := by
  show RelCT isa P (.block ((List.range 4).flatMap fun k' => leafL p k')) fun _ _ => True
  simp only [leafL, Impl.SlhDsa.AArch64.Verify.treeT, Impl.SlhDsa.AArch64.Verify.treeSig,
    Impl.SlhDsa.AArch64.Shake.layout, Layout.adrsOff, Layout.msgOff]
  rcases hA with ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ <;>
    simp only [hn, ha, hk] <;> exact taintR _ hr (by taint_decide)

/-- The arguments of the call of `thash4` of a height. -/
theorem ct_argsH (hr : Agree P [.x19]) :
    RelCT isa P (.block (thashArgs ⟨p.n, p.len⟩ Layout.oA Layout.strideA (3 * p.n + 32))) fun _ _ => True := by
  rcases hA with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    simp only [hn, thashArgs, Layout.msgOff] <;> exact taintR _ hr (by taint_decide)

/-- A lane at a height, which branches on its index's bit. -/
theorem ct_upLane {k' : Nat} (hk' : k' < 4)
    (hr : Agree P [.x19, .x21, .x22, .x23, Impl.SlhDsa.AArch64.Verify.idxReg k']) :
    RelCT isa P (Impl.SlhDsa.AArch64.Verify.forsUpLane p k') fun _ _ => True := by
  simp only [Impl.SlhDsa.AArch64.Verify.forsUpLane, Impl.SlhDsa.AArch64.Verify.treeT,
    Impl.SlhDsa.AArch64.Verify.treeSig, Impl.SlhDsa.AArch64.Shake.layout, Layout.adrsOff, Layout.msgOff]
  rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases hA with ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ <;>
    simp only [hn, ha, hk] <;> exact taintR _ hr (by taint_decide)

/-- The end of a height. -/
theorem ct_utail (hr : Agree P []) :
    RelCT isa P (.block [.addImm .x .x23 .x23 1, .subImm .x .x9 .x23 p.a]) fun _ _ => True := by
  rcases hA with ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ <;>
    simp only [ha] <;> exact taintR _ hr (by taint_decide)

/-- The roots' block. -/
theorem ct_roots (hr : Agree P [.x19, .x22]) :
    RelCT isa P (.block ((List.range 4).flatMap (rootL p) ++
      ([.addImm .x .x22 .x22 4, .subImm .x .x9 .x22 p.k, .lsr .x .x9 .x9 63] : List Instr))) fun _ _ => True := by
  show RelCT isa P (.block ((List.range 4).flatMap (fun k' => rootL p k') ++
      ([.addImm .x .x22 .x22 4, .subImm .x .x9 .x22 p.k, .lsr .x .x9 .x9 63] : List Instr))) fun _ _ => True
  simp only [rootL, Impl.SlhDsa.AArch64.Verify.treeT, Impl.SlhDsa.AArch64.Shake.layout, Layout.msgOff]
  rcases hA with ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ <;>
    simp only [hn, hk] <;> exact taintR _ hr (by taint_decide)

end

end VG.Proof.SlhDsa.AArch64.ForsPk
