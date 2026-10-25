module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.RotateExpr
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.CoreExec
import VerifiedGarbage.Proof.Framework.Bitslice.Anf

@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar.Lazy
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64.Scalar

deriving instance DecidableEq for ScalarOp

def registers : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x30]
def regIndex (r : Reg) : Nat := registers.idxOf r

def environment (logical physical : File) : File :=
  ⟨logical.regs, fun k => if k % 2 = 0 then physical.slots (k / 2)
    else physical.regs (registers.getD (k / 2) .x0)⟩

/-- Unassigned registers and preexisting slots are distinct symbolic inputs. -/
def physicalInitial : SymFile :=
  ⟨fun r => .slot (2 * regIndex r + 1), fun k => .slot (2 * k)⟩

/-- Model the physical input lanes by expressions in canonical logical lanes. -/
def symbolicLayout (layout : Layout) : SymFile :=
  layout.zipIdx.foldl (fun sf (entry, i) =>
    sf.write entry.1 (.ror (.reg (laneReg i)) entry.2)) physicalInitial

theorem environment_reg (logical physical : File) (r : Reg) :
    (Expr.slot (2 * regIndex r + 1)).eval (environment logical physical) = physical.regs r := by
  cases r <;> rfl

theorem physicalInitial_compatible (logical physical : File) :
    Compatible (environment logical physical) physicalInitial physical := by
  constructor
  · intro r; exact (environment_reg logical physical r).symm
  · intro k
    simp only [physicalInitial, Expr.eval, environment]
    rw [show 2 * k % 2 = 0 by omega, ite_eq_left rfl,
      show 2 * k / 2 = k by omega]

/-- Every listed lane has its declared physical orientation. -/
def LayoutHolds (layout : Layout) (logical physical : File) : Prop :=
  ∀ entry i, (entry, i) ∈ layout.zipIdx →
    physical.regs entry.1 = (logical.regs (laneReg i)).rotateRight entry.2

theorem symbolicLayout_compatible (layout : Layout) (logical physical : File)
    (h : LayoutHolds layout logical physical) :
    Compatible (environment logical physical) (symbolicLayout layout) physical := by
  apply List.foldlRecOn (motive := fun sf =>
    Compatible (environment logical physical) sf physical)
  · exact physicalInitial_compatible logical physical
  · intro sf hs entry he
    obtain ⟨⟨reg, offset⟩, i⟩ := entry
    constructor
    · intro q
      simp only [SymFile.write]
      split
      · rename_i hq; subst q
        exact h (reg, offset) i he
      · exact hs.1 q
    · exact hs.2

def outputExpr (p : Plan) (i : Nat) : Expr :=
  let (reg, offset) := p.output.getD i (.x0, 0)
  ((symRun p.core (symbolicLayout p.input)).regs reg).rotateNormal ((64-offset)%64)

def referenceExpr (i : Nat) : Expr :=
  ((symRun coreOps symInitial).regs (laneReg i)).rotateNormal 0

theorem plan_math (p : Plan)
    (cert : ∀ i < 25, outputExpr p i = referenceExpr i)
    (logical physical : File) (h : LayoutHolds p.input logical physical)
    (i : Nat) (hi : i < 25) :
    let (reg, offset) := p.output.getD i (.x0, 0)
    ((run p.core physical).regs reg).rotateRight ((64-offset)%64) =
      (run coreOps (environment logical physical)).regs (laneReg i) := by
  have hc := symRun_correct (environment logical physical) physical
    (symbolicLayout p.input) p.core (symbolicLayout_compatible p.input logical physical h)
  have he := congrArg (Expr.eval (environment logical physical)) (cert i hi)
  dsimp only [outputExpr, referenceExpr] at he
  rw [Expr.rotateNormal_eval, Expr.rotateNormal_eval,
    VG.Bitslice.Anf.rotateRight_zero, ← run_regs] at he
  rw [← hc.1] at he
  rcases hp : p.output.getD i (.x0, 0) with ⟨reg, offset⟩
  simpa only [hp] using he

theorem rotateRight_undo (x : Lane) (offset : Nat) (ho : offset < 64) :
    (x.rotateRight ((64-offset)%64)).rotateRight offset = x := by
  rw [VG.Bitslice.Anf.rotateRight_rotateRight]
  have hm : (((64-offset)%64)+offset)%64 = 0 := by omega
  rw [hm, VG.Bitslice.Anf.rotateRight_zero]

theorem plan_layout (p : Plan)
    (cert : ∀ i < 25, outputExpr p i = referenceExpr i)
    (hlen : p.output.length = 25)
    (bounds : ∀ entry ∈ p.output, entry.2 < 64)
    (logical physical : File) (h : LayoutHolds p.input logical physical) :
    LayoutHolds p.output (run coreOps (environment logical physical)) (run p.core physical) := by
  intro entry i he
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp he
  have hi : i < 25 := by
    have hlt := (List.getElem?_eq_some_iff.mp hget).1
    omega
  have hd : p.output.getD i (.x0, 0) = entry := by
    simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some]
  have hm := plan_math p cert logical physical h i hi
  simp only [hd] at hm
  have hb : entry.2 < 64 := bounds entry (List.mem_of_getElem? hget)
  have ht := congrArg (fun x : Lane => x.rotateRight entry.2) hm
  rw [rotateRight_undo _ _ hb] at ht
  exact ht

theorem plans_symbolic : ∀ (r : Fin 24), ∀ i < 25, outputExpr (plans[r.val]' (by exact r.isLt)) i = referenceExpr i := by decide +kernel

theorem plans_shape : ∀ r : Fin 24,
    (plan r).input.length = 25 ∧ (plan r).output.length = 25 ∧
    (plan r).finish = (plan r).output ∧
    (∀ entry ∈ (plan r).output, entry.2 < 64) ∧
    (∀ op ∈ (plan r).core, Good op) ∧ Good (plan r).iota := by decide +kernel

theorem plans_iota : ∀ r : Fin 24,
    let lane := (plan r).output.getD 0 (.x0, 0)
    (plan r).iota = .xorRor lane.1 lane.1 (plan r).constantReg lane.2 ∧
    (∀ entry ∈ (plan r).output, entry.1 ≠ (plan r).constantReg) := by decide +kernel

theorem plans_transition : ∀ r : Fin 23,
    (plan ⟨r.val, by omega⟩).finish = (plan ⟨r.val+1, by omega⟩).input := by decide +kernel


theorem plans_lane_zero : ∀ r : Fin 24, ∀ i < 25,
    ((plan r).output.getD i (.x0, 0)).1 =
      ((plan r).output.getD 0 (.x0, 0)).1 ↔ i = 0 := by decide +kernel

theorem normalize_symbolic : ∀ i < 25,
    ((symRun normalize (symbolicLayout (plan ⟨23, by decide⟩).finish)).regs
      (laneReg i)).rotateNormal 0 = (Expr.reg (laneReg i)).rotateNormal 0 := by decide +kernel


def stageLayout (n : Nat) : Layout :=
  if h : n < 24 then (plan ⟨n, h⟩).input else (plan ⟨23, by decide⟩).finish

theorem plans_stage : ∀ r : Fin 24, (plan r).finish = stageLayout (r.val+1) := by
  decide +kernel

theorem normalize_good : ∀ op ∈ normalize, Good op := by decide +kernel


end VG.Proof.Sha3.AArch64.Scalar.Lazy
