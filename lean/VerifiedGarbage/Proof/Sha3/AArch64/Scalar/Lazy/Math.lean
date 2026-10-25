module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy
import Mathlib.Tactic.IntervalCases
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.CoreExec
import VerifiedGarbage.Proof.Framework.Bitslice.Anf

@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar.Lazy
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64.Scalar

/-- Canonical logical lanes, independent of their current physical allocation. -/
def logicalState (A : Spec.Sha3.State) : File :=
  ⟨(fun r => match r with
    | .x0 => A[0]
    | .x1 => A[1]
    | .x2 => A[2]
    | .x3 => A[3]
    | .x4 => A[4]
    | .x5 => A[5]
    | .x6 => A[6]
    | .x7 => A[7]
    | .x8 => A[8]
    | .x9 => A[9]
    | .x10 => A[10]
    | .x11 => A[11]
    | .x12 => A[12]
    | .x13 => A[13]
    | .x14 => A[14]
    | .x15 => A[15]
    | .x16 => A[16]
    | .x17 => A[17]
    | .x25 => A[18]
    | .x19 => A[19]
    | .x20 => A[20]
    | .x21 => A[21]
    | .x22 => A[22]
    | .x23 => A[23]
    | .x24 => A[24]
    | _ => 0), fun _ => 0⟩

theorem logicalState_lane (A : Spec.Sha3.State) (i : Nat) (hi : i < 25) :
    (logicalState A).regs (laneReg i) = A[i] := by
  interval_cases i <;> rfl

/-- A round's scalar operations compute chi/pi/rho/theta in the declared layout. -/
theorem plan_core_state (r : Fin 24) (A : Spec.Sha3.State) (f : File)
    (h : LayoutHolds (plan r).input (logicalState A) f) :
    LayoutHolds (plan r).output
      (logicalState (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A)))))
      (run (plan r).core f) := by
  have hp := plans_shape r
  have hm := plan_layout (plan r) (plans_symbolic r) hp.2.1 hp.2.2.2.1
    (logicalState A) f h
  have hcore := core_math A (environment (logicalState A) f)
    (fun i hi => logicalState_lane A i hi)
  intro entry i he
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp he
  have hi : i < 25 := by
    have hlt := (List.getElem?_eq_some_iff.mp hget).1
    omega
  rw [hm entry i he, hcore i hi, logicalState_lane _ i hi]

theorem layout_at (layout : Layout) (logical physical : File)
    (h : LayoutHolds layout logical physical) (i : Nat) (hi : i < layout.length) :
    physical.regs (layout.getD i (.x0, 0)).1 =
      (logical.regs (laneReg i)).rotateRight (layout.getD i (.x0, 0)).2 := by
  apply h _ i
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- Building a public constant does not change any lane of this layout. -/
theorem layout_write_constant (layout : Layout) (logical physical : File)
    (h : LayoutHolds layout logical physical) (d : Reg) (v : Lane)
    (hd : ∀ entry ∈ layout, entry.1 ≠ d) :
    LayoutHolds layout logical (physical.write d v) := by
  intro entry i he
  have hm := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp he)
  simp only [File.write, ite_eq_right (hd entry hm)]
  exact h entry i he


theorem layout_of_at (layout : Layout) (logical physical : File)
    (h : ∀ i < layout.length,
      physical.regs (layout.getD i (.x0, 0)).1 =
        (logical.regs (laneReg i)).rotateRight (layout.getD i (.x0, 0)).2) :
    LayoutHolds layout logical physical := by
  intro entry i he
  have hg := List.mk_mem_zipIdx_iff_getElem?.mp he
  have hi := (List.getElem?_eq_some_iff.mp hg).1
  have hd : layout.getD i (.x0, 0) = entry := by
    simp only [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  simpa only [hd] using h i hi

theorem plan_iota_state (r : Fin 24) (A : Spec.Sha3.State) (f : File)
    (h : LayoutHolds (plan r).output (logicalState A) f) :
    LayoutHolds (plan r).finish (logicalState (Spec.Sha3.iota A r.val))
      (step (f.write (plan r).constantReg (Spec.Sha3.RC r.val)) (plan r).iota) := by
  have hp := plans_shape r
  rw [hp.2.2.1]
  apply layout_of_at
  intro i hi
  have hi25 : i < 25 := by omega
  have hval := layout_at _ _ _ h i hi
  rw [logicalState_lane A i hi25] at hval
  have hval0 := layout_at _ _ _ h 0 (by omega)
  rw [logicalState_lane A 0 (by decide)] at hval0
  have hc := (plans_iota r).2
  have memi : (plan r).output.getD i (.x0, 0) ∈ (plan r).output := by
    apply List.mem_of_getElem? (i := i)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have mem0 : (plan r).output.getD 0 (.x0, 0) ∈ (plan r).output := by
    apply List.mem_of_getElem? (i := 0)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < (plan r).output.length by omega), Option.getD_some]
  rw [(plans_iota r).1]
  simp only [step, File.write, logicalState_lane _ i hi25]
  by_cases hz : i = 0
  · subst i
    simp only [ite_true, ite_eq_right (hc _ mem0), hval0, Spec.Sha3.iota,
      Vector.getElem_set_self, VG.Bitslice.Anf.rotateRight_xor]
  · have hn := (plans_lane_zero r i hi25).not.mpr hz
    simp only [ite_eq_right hn, ite_eq_right (hc _ memi), hval,
      Spec.Sha3.iota, Vector.getElem_set, Ne.symm hz, ite_false]


def abstractRound (r : Fin 24) (f : File) : File :=
  step ((run (plan r).core f).write (plan r).constantReg (Spec.Sha3.RC r.val))
    (plan r).iota

theorem abstractRound_state (r : Fin 24) (A : Spec.Sha3.State) (f : File)
    (h : LayoutHolds (plan r).input (logicalState A) f) :
    LayoutHolds (plan r).finish (logicalState (Spec.Sha3.rnd A r.val))
      (abstractRound r f) :=
  plan_iota_state r _ _ (plan_core_state r A f h)

theorem layout_of_regs (layout : Layout) (logical f g : File)
    (h : LayoutHolds layout logical f) (hr : ∀ r, g.regs r = f.regs r) :
    LayoutHolds layout logical g := by
  intro entry i he
  rw [hr]
  exact h entry i he


end VG.Proof.Sha3.AArch64.Scalar.Lazy
