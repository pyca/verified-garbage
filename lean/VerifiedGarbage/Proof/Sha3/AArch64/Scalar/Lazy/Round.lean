module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.CoreExec
import VerifiedGarbage.Proof.Framework.Bitslice.Anf
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
public import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `Sha3.AArch64.Scalar.Lazy.Math`, which only this module used -/

section

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
  iterate 25 (rcases i with _ | i; rfl)
  exact absurd hi (by omega_arith)

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
  have hval0 := layout_at _ _ _ h 0 (by omega_using [hi])
  rw [logicalState_lane A 0 (by decide)] at hval0
  have hc := (plans_iota r).2
  have memi : (plan r).output.getD i (.x0, 0) ∈ (plan r).output := by
    apply List.mem_of_getElem? (i := i)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have mem0 : (plan r).output.getD 0 (.x0, 0) ∈ (plan r).output := by
    apply List.mem_of_getElem? (i := 0)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < (plan r).output.length by omega_using [hi]), Option.getD_some]
  rw [(plans_iota r).1]
  simp only [step, File.write, logicalState_lane _ i hi25]
  by_cases hz : i = 0
  · subst i
    simp only [ite_true, ite_eq_right (hc _ mem0), hval0, Spec.Sha3.iota,
      Vector.getElem_set_self, VG.Bitslice.Anf.rotateRight_xor]
  · have hn := (not_congr (plans_lane_zero r i hi25)).mpr hz
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

end

end

/-! ### `Sha3.AArch64.Scalar.Lazy.Constant`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Lazy.Constant
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64

structure ConstantKeep (d : Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  vec : s'.v = s.v
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem constant_ok (d : Reg) (r : Nat) (s : State) :
    WP isa (.block (constant d r)) s fun s' =>
      ConstantKeep d s s' ∧ s'.gpr d = Sha3.Vector.constantLow (Spec.Sha3.RC r) := by
  by_cases h1 : (Spec.Sha3.RC r).extractLsb' 16 16 = 0 <;>
    by_cases h2 : (Spec.Sha3.RC r).extractLsb' 32 16 = 0 <;>
    by_cases h3 : (Spec.Sha3.RC r).extractLsb' 48 16 = 0
  all_goals
    simp only [constant, h1, h2, h3, ite_true, ite_false,
      List.cons_append, List.nil_append]
    repeat' apply WP.cons rfl
    apply wp_nil
    refine ⟨⟨?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · intro r hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    · simp only [Sha3.Vector.constantLow, h1, h2, h3, ite_true, ite_false,
        Sha3.Vector.movkValue, RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq]

end VG.Proof.Sha3.AArch64.Scalar.Lazy.Constant

end

end


@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar.Lazy
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64.Scalar

def machineFile (s : State) : File :=
  ⟨s.gpr, fun k => vdword (s.v (slotV k)) 0⟩

structure Keep (s t : State) : Prop where
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  vec : ∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → t.v v = s.v v

/-- A complete machine-code round realizes the checked rotated lane layout. -/
theorem round_ok (r : Fin 24) (A : Spec.Sha3.State) (s : State)
    (h : LayoutHolds (plan r).input (logicalState A) (machineFile s)) :
    WP isa (.block (round r)) s fun t =>
      LayoutHolds (plan r).finish (logicalState (Spec.Sha3.rnd A r.val)) (machineFile t) ∧
      Keep s t := by
  let f := machineFile s
  have hrel : VectorFileRel f s := ⟨fun _ => rfl, fun _ _ => rfl⟩
  have hp := plans_shape r
  obtain ⟨t, ht, hrt, hm, hrd, hwr, hsp, hv⟩ :=
    vector_list_ok (plan r).core hp.2.2.2.2.1 f s hrel
  unfold round
  rw [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨t, ht, ?_⟩
  rw [WP.block_append_iff]
  refine (Constant.constant_ok (plan r).constantReg r.val t).mono fun u ⟨hk, hu⟩ => ?_
  rw [VG.Proof.Sha3.AArch64.Sha3.Vector.constantLow_RC r.val r.isLt] at hu
  let f1 := (run (plan r).core f).write (plan r).constantReg (Spec.Sha3.RC r.val)
  have hru : VectorFileRel f1 u := by
    constructor
    · intro q
      by_cases hq : q = (plan r).constantReg
      · subst q
        simpa only [f1, File.write, ite_true] using hu
      · simp only [f1, File.write, ite_eq_right hq]
        exact (hk.gpr q hq).trans (hrt.regs q)
    · intro k hkb
      rw [hk.vec]
      exact hrt.slots k hkb
  obtain ⟨v, hvexec, hrv, hvm, hvrd, hvwr, hvsp, hvvec⟩ :=
    vector_step_ok (plan r).iota hp.2.2.2.2.2 f1 u hru
  refine WP.of_runBlock ⟨v, hvexec, ?_⟩
  refine ⟨?_, ⟨hvm.trans (hk.mem.trans hm), hvrd.trans (hk.rd.trans hrd),
    hvwr.trans (hk.wr.trans hwr), hvsp.trans (hk.sp.trans hsp), ?_⟩⟩
  · exact layout_of_regs _ _ _ _ (abstractRound_state r A f h) hrv.regs
  · intro w h24 h25 h28 h29
    exact (hvvec w h24 h25 h28 h29).trans
      ((congrFun hk.vec w).trans (hv w h24 h25 h28 h29))

end VG.Proof.Sha3.AArch64.Scalar.Lazy
