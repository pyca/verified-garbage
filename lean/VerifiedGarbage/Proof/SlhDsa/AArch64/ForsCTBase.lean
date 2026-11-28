module

-- separate module: the taint checks of `forsSign`'s blocks, rebuilt only when its blocks change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsFront
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTSets
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Sz
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsFront
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTSets
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.Sz
public meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.RelCT

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign` is constant time, its blocks

The taint analysis checks each block of `forsSign`
(`Impl/SlhDsa/AArch64/Fors.lean`) from the stack pointer and the registers
both runs agree on, for each of the six parameter sets (`Fors.As`): `x19`
(`scratch`), `x24` (the tree's signature) and the counters `x23`, `x25`,
`x26` and `x27`, as each block needs them. `kp` (`x20`) and the tree's
index (`x21`) are secret: they reach only stores and masks.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.AArch64 (Layout setField setFieldR copyWords zeroWords mulN movV lea thashArgs)
open VG.Impl.SlhDsa.AArch64.Fors
open VG.Proof.SlhDsa.AArch64.TreeBase (taintR)

section
variable {P : State → State → Prop}

/-- What the checks need of two related states: the same stack pointer and
registers `rs`. -/
abbrev Agree (P : State → State → Prop) (rs : List Reg) : Prop :=
  ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r

/-- An empty block. -/
theorem ct_nil (hr : Agree P []) : RelCT isa P (.block []) fun _ _ => True :=
  taintR _ hr (by taint_decide)

/-- `x26 ← 0`. -/
theorem ct_j0 (hr : Agree P []) : RelCT isa P (.block [.movz .x .x26 0 0]) fun _ _ => True :=
  taintR _ hr (by taint_decide)

variable {p : Params} (hz : Sz p) (hA : As p)
include hz hA

omit hz in
/-- The prologue and the indices. -/
theorem ct_pro (hr : Agree P [.x0, .x1]) :
    RelCT isa P (.block (pro ++ indices p.a p.k ++ ([.movz .x .x23 0 0, .movz .x .x27 0 0] : List Instr)))
      fun _ _ => True := by
  rcases hA with ⟨-, ha, hk⟩ | ⟨-, ha, hk⟩ | ⟨-, ha, hk⟩ | ⟨-, ha, hk⟩ | ⟨-, ha, hk⟩ | ⟨-, ha, hk⟩ <;>
    simp only [ha, hk] <;> exact taintR _ hr (by taint_decide)

/-- The arguments of a call of `thash4` on the lanes `A`. -/
theorem ct_argsA (hr : Agree P [.x19]) :
    RelCT isa P (.block (thashArgs ⟨p.n, p.len⟩ Layout.oA Layout.strideA (2 * p.n + 32))) fun _ _ => True := by
  have hl := hz.len
  rcases hA with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    simp only [hl, hn] <;> exact taintR _ hr (by taint_decide)

/-- The arguments of `pkFors`' call of `thash4` on the lanes `B`. -/
theorem ct_argsB (hr : Agree P [.x19]) :
    RelCT isa P (.block (thashArgs ⟨p.n, p.len⟩ Layout.oB Layout.strideB (p.n + 32 + p.k * p.n)))
      fun _ _ => True := by
  have hl := hz.len
  rcases hA with ⟨hn, -, hk⟩ | ⟨hn, -, hk⟩ | ⟨hn, -, hk⟩ | ⟨hn, -, hk⟩ | ⟨hn, -, hk⟩ | ⟨hn, -, hk⟩ <;>
    simp only [hl, hn, hk] <;> exact taintR _ hr (by taint_decide)

/-- The lanes for the private key values. -/
theorem ct_lanes (hr : Agree P [.x19, .x25, .x26, .x27]) :
    RelCT isa P (.block (([.add .x .x10 .x27 .x25, .add .x .x10 .x10 .x26] : List Instr) ++
      (List.range 4).flatMap (fun k' => leafAdrs ⟨p.n, p.len⟩ 6 k' ++
        copyWords .x19 (Layout.laneA k' + (⟨p.n, p.len⟩ : Layout).msgOff) .x19 Layout.oSkSeed
          ((⟨p.n, p.len⟩ : Layout).n / 8)))) fun _ _ => True := by
  have hl := hz.len
  rcases hA with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    simp only [hl, hn] <;> exact taintR _ hr (by taint_decide)

/-- The capture of the private key values, and the type of the leaves. -/
theorem ct_cap (hr : Agree P [.x19, .x24, .x25, .x26]) :
    RelCT isa P (.block (([.add .x .x11 .x25 .x26] : List Instr) ++
      (List.range 4).flatMap (captureSk ⟨p.n, p.len⟩) ++
      (List.range 4).flatMap (fun k' => setField .x19 (Layout.laneA k' + (⟨p.n, p.len⟩ : Layout).adrsOff + 16) 3)))
      fun _ _ => True := by
  have hl := hz.len
  rcases hA with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    simp only [hl, hn] <;> exact taintR _ hr (by taint_decide)

/-- The leaves to the nodes, and the next four. -/
theorem ct_out (hr : Agree P [.x19, .x26]) :
    RelCT isa P (.block (([Impl.SlhDsa.AArch64.Thash4.mov .x10 .x26] : List Instr) ++
      mulN (⟨p.n, p.len⟩ : Layout).n .x10 .x11 ++ ([.add .x .x10 .x10 .x19] : List Instr) ++
      (List.range 4).flatMap (fun k' =>
        copyWords .x10 (Layout.oN + (⟨p.n, p.len⟩ : Layout).n * k') .x19
          (Layout.laneA k' + (⟨p.n, p.len⟩ : Layout).msgOff) ((⟨p.n, p.len⟩ : Layout).n / 8)) ++
      ([.addImm .x .x26 .x26 4, .subImm .x .x9 .x26 (2 ^ s p.a)] : List Instr))) fun _ _ => True := by
  have hl := hz.len
  rcases hA with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    simp only [hl, hn, ha] <;> exact taintR _ hr (by taint_decide)

omit hz in
/-- The parameters and arguments of `levels` for a subtree. -/
theorem ct_sb (hr : Agree P [.x19, .x24, .x25, .x27]) :
    RelCT isa P (.block (([.addImm .x .x10 .x24 (⟨p.n, p.len⟩ : Layout).n, .add .x .x11 .x27 .x25] : List Instr) ++
      Impl.SlhDsa.AArch64.Tree.setParams (.reg .x25) (.reg .x11) (.imm 3) (.reg .x20) ++
      ([Impl.SlhDsa.AArch64.Thash4.mov .x0 .x19] : List Instr) ++ lea .x1 .x19 Layout.oN ++
      movV .x2 (2 ^ s p.a) ++
      ([.movz .x .x3 0 0, Impl.SlhDsa.AArch64.Thash4.mov .x4 .x10, Impl.SlhDsa.AArch64.Thash4.mov .x5 .x21] :
        List Instr))) fun _ _ => True := by
  rcases hA with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    simp only [hn, ha] <;> exact taintR _ hr (by taint_decide)

omit hz in
/-- The subtree's root to the subtree roots. -/
theorem ct_root (hr : Agree P [.x19, .x25]) :
    RelCT isa P (.block (([.lsr .x .x10 .x25 (s p.a)] : List Instr) ++ mulN (⟨p.n, p.len⟩ : Layout).n .x10 .x11 ++
      ([.add .x .x10 .x10 .x19] : List Instr) ++
      copyWords .x10 Layout.oRoots .x19 Layout.oN ((⟨p.n, p.len⟩ : Layout).n / 8))) fun _ _ => True := by
  rcases hA with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    simp only [hn, ha] <;> exact taintR _ hr (by taint_decide)

omit hz in
/-- The next subtree. -/
theorem ct_nextSub (hr : Agree P []) :
    RelCT isa P (.block (([.addImm .x .x25 .x25 (2 ^ s p.a)] : List Instr) ++ movV .x10 (2 ^ p.a) ++
      ([.sub .x .x9 .x25 .x10] : List Instr))) fun _ _ => True := by
  rcases hA with ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ | ⟨-, ha, -⟩ <;>
    simp only [ha] <;> exact taintR _ hr (by taint_decide)

omit hz in
/-- The tree's index, its signature zeroed, the first subtree. -/
theorem ct_tree0 (hr : Agree P [.x19, .x23, .x24]) :
    RelCT isa P (.block (([.lsl .x .x9 .x23 3, .add .x .x9 .x9 .x19, .ldr .x .x21 .x9 Layout.oFidx] : List Instr) ++
      zeroWords .x24 0 ((p.a + 1) * (⟨p.n, p.len⟩ : Layout).n / 8) ++ ([.movz .x .x25 0 0] : List Instr)))
      fun _ _ => True := by
  rcases hA with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    simp only [hn, ha] <;> exact taintR _ hr (by taint_decide)

omit hz in
/-- The subtree roots to the nodes, and the parameters and arguments of
`levels` above the subtrees. -/
theorem ct_top (hr : Agree P [.x19, .x24, .x27]) :
    RelCT isa P (.block (copyWords .x19 Layout.oN .x19 Layout.oRoots (2 ^ (p.a - s p.a) * (⟨p.n, p.len⟩ : Layout).n / 8) ++
      ([.addImm .x .x10 .x24 ((⟨p.n, p.len⟩ : Layout).n + s p.a * (⟨p.n, p.len⟩ : Layout).n)] : List Instr) ++
      Impl.SlhDsa.AArch64.Tree.setParams (.imm 0) (.reg .x27) (.imm 3) (.reg .x20) ++
      ([Impl.SlhDsa.AArch64.Thash4.mov .x0 .x19] : List Instr) ++ lea .x1 .x19 Layout.oN ++
      movV .x2 (2 ^ (p.a - s p.a)) ++
      ([.movz .x .x3 (BitVec.ofNat 16 (s p.a)) 0, Impl.SlhDsa.AArch64.Thash4.mov .x4 .x10,
        Impl.SlhDsa.AArch64.Thash4.mov .x5 .x21] : List Instr))) fun _ _ => True := by
  rcases hA with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    simp only [hn, ha] <;> exact taintR _ hr (by taint_decide)

/-- The tree's root to lane 0 of the lanes `B`. -/
theorem ct_rootB (hr : Agree P [.x19, .x23]) :
    RelCT isa P (.block (([Impl.SlhDsa.AArch64.Thash4.mov .x10 .x23] : List Instr) ++
      mulN (⟨p.n, p.len⟩ : Layout).n .x10 .x11 ++ ([.add .x .x10 .x10 .x19] : List Instr) ++
      copyWords .x10 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).msgOff) .x19 (rootOff p.a)
        ((⟨p.n, p.len⟩ : Layout).n / 8))) fun _ _ => True := by
  have hl := hz.len
  rcases hA with ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ | ⟨hn, ha, -⟩ <;>
    simp only [hl, hn, ha] <;> exact taintR _ hr (by taint_decide)

omit hz in
/-- The next tree. -/
theorem ct_nextTree (hr : Agree P []) :
    RelCT isa P (.block (([.addImm .x .x24 .x24 ((p.a + 1) * (⟨p.n, p.len⟩ : Layout).n)] : List Instr) ++
      movV .x10 (2 ^ p.a) ++ ([.add .x .x27 .x27 .x10, .addImm .x .x23 .x23 1, .subImm .x .x9 .x23 p.k] : List Instr)))
      fun _ _ => True := by
  rcases hA with ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ | ⟨hn, ha, hk⟩ <;>
    simp only [hn, ha, hk] <;> exact taintR _ hr (by taint_decide)

/-- The fields of `T_k`'s address. -/
theorem ct_pkFields (hr : Agree P [.x19]) :
    RelCT isa P (.block (setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 16) 4 ++
      setFieldR .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 20) .x20 ++
      setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 24) 0 ++
      setField .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 28) 0)) fun _ _ => True := by
  have hl := hz.len
  rcases hA with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    simp only [hl, hn] <;> exact taintR _ hr (by taint_decide)

/-- The public key to `oMsg`. -/
theorem ct_pkCopy (hr : Agree P [.x19]) :
    RelCT isa P (.block (copyWords .x19 Layout.oMsg .x19 (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).msgOff)
      ((⟨p.n, p.len⟩ : Layout).n / 8))) fun _ _ => True := by
  have hl := hz.len
  rcases hA with ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ <;>
    simp only [hl, hn] <;> exact taintR _ hr (by taint_decide)

omit hz hA in
/-- The epilogue. -/
theorem ct_epi (hr : Agree P [.x19]) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.restoreRegs 2 saved)) fun _ _ => True :=
  taintR _ hr (by taint_decide)

end

end VG.Proof.SlhDsa.AArch64.Fors
