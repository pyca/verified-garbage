module

-- separate module: the taint checks of `xmssPk`'s blocks, rebuilt only when its blocks change

public import VerifiedGarbage.Impl.SlhDsa.AArch64.Verify
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TreeBase
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Sz
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public meta import VerifiedGarbage.Impl.SlhDsa.AArch64.Verify
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.TreeBase
public meta import VerifiedGarbage.Proof.SlhDsa.AArch64.Sz
public meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public meta import VerifiedGarbage.Proof.Framework.Taint
public meta import VerifiedGarbage.Proof.Framework.RelCT

/-!
# SLH-DSA (SHAKE) on AArch64: `xmssPk` is constant time, its blocks

The taint analysis checks each block of `xmssPk` (`Impl/SlhDsa/AArch64/Verify.lean`)
from the stack pointer and the registers both runs agree on: `x19`
(`scratch`), `x20` (`idx`), `x21` (`sig`), `x22` (the group's first chain),
`x23` (the step), `x25` and `x26` (the height and `idx` shifted), and the
registers a block's branches and addresses read, which hold functions of
the digits and the counters, the same in both runs (`VerifyXmssCT.lean`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.XmssPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.AArch64 (Layout thashArgs)
open VG.Proof.SlhDsa.AArch64.TreeBase (taintR)

/-- Two runs' states agree on the stack pointer and the registers `rs`. -/
abbrev Ag (P : State → State → Prop) (rs : List Reg) : Prop :=
  ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r

section
variable {P : State → State → Prop}

theorem ct_xnil (hr : Ag P []) : RelCT isa P (.block []) fun _ _ => True :=
  taintR _ hr (by taint_decide)

theorem ct_mid (hr : Ag P []) :
    RelCT isa P (.block [Impl.SlhDsa.AArch64.Thash4.mov .x23 .x24, .subImm .x .x9 .x24 15]) fun _ _ => True :=
  taintR _ hr (by taint_decide)

theorem ct_stail (hr : Ag P []) :
    RelCT isa P (.block [.addImm .x .x23 .x23 1, .subImm .x .x9 .x23 15]) fun _ _ => True :=
  taintR _ hr (by taint_decide)

theorem ct_pinit (hr : Ag P [.x20]) :
    RelCT isa P (.block [.movz .x .x25 0 0, Impl.SlhDsa.AArch64.Thash4.mov .x26 .x20]) fun _ _ => True :=
  taintR _ hr (by taint_decide)

variable {p : Params} (hz : Sz p)
include hz

/-- The prologue and the digits. -/
theorem ct_xentry (hr : Ag P [.x0]) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.Verify.xpro ++ Impl.SlhDsa.AArch64.Xmss.digits ⟨p.n, p.len⟩ ++
      ([.movz .x .x22 0 0] : List Instr))) fun _ _ => True := by
  have hl := hz.len
  rcases hz.nv with hn | hn | hn <;> simp only [hl, hn] <;> exact taintR _ hr (by taint_decide)

/-- A group's lanes. -/
theorem ct_chainLanes (hr : Ag P [.x19, .x20, .x21, .x22]) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.Verify.chainLanes p)) fun _ _ => True := by
  have hl := hz.len
  simp only [Impl.SlhDsa.AArch64.Verify.chainLanes, Impl.SlhDsa.AArch64.Verify.chainOf,
    Impl.SlhDsa.AArch64.Verify.chainSig, Impl.SlhDsa.AArch64.Shake.layout, Layout.adrsOff, Layout.msgOff]
  rcases hz.nv with hn | hn | hn <;> simp only [hl, hn] <;> exact taintR _ hr (by taint_decide)

/-- A group's ends, to lane 0 of `B`. -/
theorem ct_ends (hr : Ag P [.x19, .x22]) :
    RelCT isa P (.block ((List.range 4).flatMap (fun k => Impl.SlhDsa.AArch64.Verify.chainOf p k ++
      ([Impl.SlhDsa.AArch64.Thash4.mov .x12 .x10] : List Instr) ++ Impl.SlhDsa.AArch64.mulN p.n .x12 .x13 ++ ([.add .x .x12 .x12 .x19] : List Instr) ++
      Impl.SlhDsa.AArch64.copyWords .x12 (Layout.laneB 0 + (p.n + 32)) .x19 (Layout.laneA k + (p.n + 32)) (p.n / 8)) ++
      ([.addImm .x .x22 .x22 4, .subImm .x .x9 .x22 p.len, .lsr .x .x9 .x9 63] : List Instr))) fun _ _ => True := by
  have hl := hz.len
  simp only [Impl.SlhDsa.AArch64.Verify.chainOf]
  rcases hz.nv with hn | hn | hn <;> simp only [hl, hn] <;> exact taintR _ hr (by taint_decide)

/-- A step's hash addresses. -/
theorem ct_hfields (hr : Ag P [.x19, .x23]) :
    RelCT isa P (.block ((List.range 4).flatMap fun k => Impl.SlhDsa.AArch64.setFieldR .x19
      (Layout.laneA k + p.n + 28) .x23)) fun _ _ => True := by
  rcases hz.nv with hn | hn | hn <;> simp only [hn] <;> exact taintR _ hr (by taint_decide)

/-- The arguments of a step's call of `thash4`. -/
theorem ct_argsS (hr : Ag P [.x19]) :
    RelCT isa P (.block (thashArgs ⟨p.n, p.len⟩ Layout.oA Layout.strideA (2 * p.n + 32))) fun _ _ => True := by
  rcases hz.nv with hn | hn | hn <;> simp only [hn, thashArgs, Layout.msgOff] <;>
    exact taintR _ hr (by taint_decide)

/-- The arguments of the call of `thash4` of a height. -/
theorem ct_argsP (hr : Ag P [.x19]) :
    RelCT isa P (.block (thashArgs ⟨p.n, p.len⟩ Layout.oA Layout.strideA (3 * p.n + 32))) fun _ _ => True := by
  rcases hz.nv with hn | hn | hn <;> simp only [hn, thashArgs, Layout.msgOff] <;>
    exact taintR _ hr (by taint_decide)

/-- The arguments of the call of `thash4` of the WOTS⁺ public key. -/
theorem ct_argsW (hr : Ag P [.x19]) :
    RelCT isa P (.block (thashArgs ⟨p.n, p.len⟩ Layout.oB Layout.strideB (p.n + 32 + p.len * p.n)))
      fun _ _ => True := by
  have hl := hz.len
  rcases hz.nv with hn | hn | hn <;> simp only [hl, hn, thashArgs, Layout.msgOff] <;>
    exact taintR _ hr (by taint_decide)

/-- The head of `restoreLane k`: chain and digit of lane `k`, and `x13 ← [j < digit]`. -/
theorem ct_rhead {k : Nat} (hk : k < 4) (hr : Ag P [.x19, .x22, .x23]) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.Verify.chainOf p k ++ ([.sub .x .x13 .x23 .x11, .lsr .x .x13 .x13 63] : List Instr)))
      fun _ _ => True := by
  have hl := hz.len
  simp only [Impl.SlhDsa.AArch64.Verify.chainOf]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases hz.nv with hn | hn | hn <;> simp only [hl, hn] <;> exact taintR _ hr (by taint_decide)

/-- The copy of `restoreLane k`: lane `k`'s signature value back. -/
theorem ct_rcopy {k : Nat} (hk : k < 4) (hr : Ag P [.x19, .x10, .x21]) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.Verify.chainSig p ++
      Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA k + (p.n + 32)) .x12 0 (p.n / 8))) fun _ _ => True := by
  simp only [Impl.SlhDsa.AArch64.Verify.chainSig]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases hz.nv with hn | hn | hn <;> simp only [hn] <;> exact taintR _ hr (by taint_decide)

/-- The fields of lane 0 of `B`'s address. -/
theorem ct_fieldsB (hr : Ag P [.x19, .x20]) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + p.n + 16) 1 ++
      Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneB 0 + p.n + 20) .x20 ++
      Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + p.n + 24) 0 ++
      Impl.SlhDsa.AArch64.setField .x19 (Layout.laneB 0 + p.n + 28) 0)) fun _ _ => True := by
  rcases hz.nv with hn | hn | hn <;> simp only [hn] <;> exact taintR _ hr (by taint_decide)

/-- The WOTS⁺ public key to lane 0 of `A`. -/
theorem ct_copyW (hr : Ag P [.x19]) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA 0 + (p.n + 32)) .x19
      (Layout.laneB 0 + (p.n + 32)) (p.n / 8))) fun _ _ => True := by
  rcases hz.nv with hn | hn | hn <;> simp only [hn] <;> exact taintR _ hr (by taint_decide)

/-- The first block of a height. -/
theorem ct_pb1 (hr : Ag P [.x21, .x25, .x26]) :
    RelCT isa P (.block ([Impl.SlhDsa.AArch64.Thash4.mov .x12 .x25] ++ Impl.SlhDsa.AArch64.mulN p.n .x12 .x13 ++
      ([.add .x .x12 .x12 .x21, .addImm .x .x12 .x12 (p.len * p.n), .movz .x .x9 1 0, .logic .and .x .x9 .x26 .x9] : List Instr)))
      fun _ _ => True := by
  have hl := hz.len
  rcases hz.nv with hn | hn | hn <;> simp only [hl, hn] <;> exact taintR _ hr (by taint_decide)

/-- The branch of a height, on bit `z` of `idx`. -/
theorem ct_pite (hr : Ag P [.x9, .x12, .x19]) :
    RelCT isa P (.ite (.zero .x .x9)
      (.block (Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA 0 + (p.n + 32) + p.n) .x12 0 (p.n / 8)))
      (.block (Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA 0 + (p.n + 32) + p.n) .x19 (Layout.laneA 0 + (p.n + 32))
          (p.n / 8) ++ Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA 0 + (p.n + 32)) .x12 0 (p.n / 8))))
      fun _ _ => True := by
  rcases hz.nv with hn | hn | hn <;> simp only [hn] <;> exact taintR _ hr (by taint_decide)

/-- The fields of a height's address. -/
theorem ct_pfields (hr : Ag P [.x19, .x25, .x26]) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.setField .x19 (Layout.laneA 0 + p.n + 16) 2 ++
      Impl.SlhDsa.AArch64.setField .x19 (Layout.laneA 0 + p.n + 20) 0 ++
      ([.addImm .x .x10 .x25 1] : List Instr) ++ Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA 0 + p.n + 24) .x10 ++
      ([.lsr .x .x26 .x26 1] : List Instr) ++ Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA 0 + p.n + 28) .x26)) fun _ _ => True := by
  rcases hz.nv with hn | hn | hn <;> simp only [hn] <;> exact taintR _ hr (by taint_decide)

omit hz in
/-- The end of a height. -/
theorem ct_ptail (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9) (hr : Ag P []) :
    RelCT isa P (.block [.addImm .x .x25 .x25 1, .subImm .x .x9 .x25 p.hp]) fun _ _ => True := by
  rcases hh with h | h | h | h <;> simp only [h] <;> exact taintR _ hr (by taint_decide)

/-- The root to `oMsg`, and the restores. -/
theorem ct_xepi (hr : Ag P [.x19]) :
    RelCT isa P (.block (Impl.SlhDsa.AArch64.copyWords .x19 Layout.oMsg .x19 (Layout.laneA 0 + (p.n + 32)) (p.n / 8) ++
      Impl.SlhDsa.AArch64.restoreRegs 1 Impl.SlhDsa.AArch64.Verify.xsaved)) fun _ _ => True := by
  rcases hz.nv with hn | hn | hn <;> simp only [hn] <;> exact taintR _ hr (by taint_decide)

end

end VG.Proof.SlhDsa.AArch64.XmssPk
