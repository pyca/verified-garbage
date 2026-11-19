module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.VectorLower
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lower
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Stages
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Sha3.AArch64.Scalar.Lower`, which this module and modules that import it used -/

section

/-! ### `Sha3.AArch64.Scalar.CoreExec`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

instance (op : ScalarOp) : Decidable (Good op) := by
  cases op <;> unfold Good <;> infer_instance

theorem core_good : ∀ op ∈ coreOps, Good op := by decide +kernel

theorem core_math (A : Spec.Sha3.State) (f : File) (h : Holds laneReg A f) :
    Holds laneReg (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A))))
      (run coreOps f) := by
  have hm := chi_correct _ _ (rhoPi_correct _ _ (theta_correct A f h))
  simpa only [coreOps, run, List.foldl_append] using hm

end VG.Proof.Sha3.AArch64.Scalar

end

end

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

private theorem read_x (s : VG.AArch64.State) (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, Size.bits, BitVec.setWidth_eq]
private theorem write_gpr (s : VG.AArch64.State) (d r : Reg) (v : BitVec 64) :
    (s.write .x d v).gpr r = if r = d then v else s.gpr r := by
  simp only [RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq]

private theorem rotate_zero (x : BitVec 64) : x.rotateRight 0 = x := by
  simp only [BitVec.rotateRight, Nat.zero_mod, BitVec.rotateRightAux,
    BitVec.ushiftRight_zero, Nat.sub_zero, BitVec.shiftLeft_eq_zero (by decide : 64 ≤ 64), BitVec.or_zero]

/-- Every scalar register value agrees with the abstract file. -/
def RegRel (f : File) (s : VG.AArch64.State) : Prop := ∀ r, s.gpr r = f.regs r

/-- Register-only abstract operations run through the existing ISA. -/
theorem reg_lower_ok (op : ScalarOp) (hgood : Good op)
    (hmem : ∀ k r, op ≠ .spill k r) (hload : ∀ r k, op ≠ .reload r k)
    (f : File) (s : VG.AArch64.State) (hr : RegRel f s) :
    ∃ s', runBlock isa (lower op) s = some s' ∧ RegRel (step f op) s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.v = s.v := by
  change ∀ r, s.gpr r = f.regs r at hr
  cases op with
  | spill k r => exact False.elim (hmem k r rfl)
  | reload r k => exact False.elim (hload r k rfl)
  | xor d a b =>
    refine ⟨s.write .x d (s.gpr a ^^^ s.gpr b), ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [lower, runBlock_cons, exec_logic, read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | move d a =>
    refine ⟨s.write .x d (s.gpr a), ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [lower, runBlock_cons, exec_addImm_x (by decide : 0 < 4096),
        read_x, show (BitVec.ofNat 64 0) = 0 from rfl, Size.bits, runStep_some, runBlock_nil]
      exact congrArg (fun v => some (s.write .x d v)) (BitVec.add_zero (s.gpr a))
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | ror d a n =>
    refine ⟨s.write .x d ((s.gpr a).rotateRight n), ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [lower, runBlock_cons, exec_ror_x hgood, read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | bic d a b =>
    refine ⟨s.write .x d (s.gpr a &&& ~~~s.gpr b), ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [lower, runBlock_cons, exec_bicRor (by decide : 0 < Size.x.bits),
        read_x, rotate_zero, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | bicRor d a b n =>
    refine ⟨s.write .x d (s.gpr a &&& ~~~(s.gpr b).rotateRight n), ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [lower, runBlock_cons, exec_bicRor (show n < Size.x.bits from hgood),
        read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | xorRor d a b n =>
    refine ⟨s.write .x d (s.gpr a ^^^ (s.gpr b).rotateRight n), ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [lower, runBlock_cons, exec_logicRor (show n < Size.x.bits from hgood),
        read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]

end VG.Proof.Sha3.AArch64.Scalar

end

end

/-! ### `Sha3.AArch64.Scalar.Scheduled`, which only this module used -/

section

@[expose] public section

end

end


@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

structure VectorFileRel (f : File) (s : VG.AArch64.State) : Prop where
  regs : ∀ r, s.gpr r = f.regs r
  slots : ∀ k < 2, vdword (s.v (slotV k)) 0 = f.slots k

private theorem slotV_eq {j k : Nat} (hj : j < 2) (hk : k < 2) :
    slotV j = slotV k ↔ j = k := by
  have h : ∀ j < 2, ∀ k < 2, (slotV j = slotV k ↔ j = k) := by decide
  exact h j hj k hk

private theorem slotV_ne (k : Nat) (v : VReg) (h24 : v ≠ .v24) (h25 : v ≠ .v25) :
    v ≠ slotV k := by
  unfold slotV tempSlotV
  split <;> with_reducible assumption

/-- Every instruction realizes its abstract operation without changing memory. -/
theorem vector_step_ok (op : ScalarOp) (hg : Good op) (f : File) (s : VG.AArch64.State)
    (hr : VectorFileRel f s) :
    ∃ s', runBlock isa (lowerVector op) s = some s' ∧ VectorFileRel (step f op) s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → s'.v v = s.v v) := by
  cases op with
  | spill k a =>
    have hk := hg.1
    refine ⟨s.setV (slotV k) (ofVDwords (s.gpr a) (s.gpr a)), ?_, ⟨?_, ?_⟩,
      rfl, rfl, rfl, rfl, ?_⟩
    · simp only [lowerVector, runBlock_cons, exec, reduceVOpEval, Option.map_some, runStep_some, runBlock_nil]
    · intro r; exact hr.regs r
    · intro j hj
      simp only [step, RegUpd.v_setV]
      by_cases he : j = k
      · subst j
        simp only [ite_true, vdword_ofVDwords_0, hr.regs]
      · simp only [ite_eq_right he, ite_eq_right ((not_congr (slotV_eq hj hk)).mpr he), hr.slots j hj]
    · intro v h24 h25 _ _
      exact RegUpd.v_setV_of_ne s _ (slotV_ne k v h24 h25)
  | reload d k =>
    have hk := hg.1
    refine ⟨s.write .x d (vdword (s.v (slotV k)) 0), ?_, ⟨?_, ?_⟩,
      rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩
    · simp only [lowerVector, runBlock_cons, exec, Size.bits, Nat.zero_mul,
        show 0 < 128 from by decide, ite_true, runStep_some, runBlock_nil]
      rfl
    · intro r
      simp only [step, File.write, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq, hr.slots k hk]
      split <;> simp only [hr.regs]
    · intro j hj; exact hr.slots j hj
  | _ =>
    obtain ⟨s', hs, hregs, hm, hrd, hwr, hsp, hv⟩ :=
      reg_lower_ok _ hg (by intro k r h; cases h) (by intro r k h; cases h) f s hr.regs
    refine ⟨s', hs, ⟨hregs, ?_⟩, hm, hrd, hwr, hsp, fun v _ _ _ _ => congrFun hv v⟩
    · intro k hk
      rw [hv]
      exact hr.slots k hk

private theorem block_append (xs ys : List Instr) (s : VG.AArch64.State) :
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    change (isa.exec x s).bind (fun s' => runBlock isa (xs ++ ys) s') =
      ((isa.exec x s).bind (runBlock isa xs)).bind (runBlock isa ys)
    rw [Option.bind_assoc]
    exact congrArg (Option.bind (isa.exec x s)) (funext fun s' => ih s')

theorem vector_list_ok (ops : List ScalarOp) (hg : ∀ op ∈ ops, Good op)
    (f : File) (s : VG.AArch64.State) (hr : VectorFileRel f s) :
    ∃ s', runBlock isa (ops.flatMap lowerVector) s = some s' ∧ VectorFileRel (run ops f) s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → s'.v v = s.v v) := by
  induction ops generalizing f s with
  | nil => exact ⟨s, rfl, hr, rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩
  | cons op ops ih =>
    obtain ⟨s₁, hs₁, hr₁, hm₁, hrd₁, hwr₁, hsp₁, hv₁⟩ :=
      vector_step_ok op (hg op (List.mem_cons_self ..)) f s hr
    obtain ⟨s₂, hs₂, hr₂, hm₂, hrd₂, hwr₂, hsp₂, hv₂⟩ :=
      ih (fun op ho => hg op (List.mem_cons_of_mem _ ho)) (step f op) s₁ hr₁
    refine ⟨s₂, ?_, hr₂, hm₂.trans hm₁, hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁,
      fun v h24 h25 h28 h29 => (hv₂ v h24 h25 h28 h29).trans (hv₁ v h24 h25 h28 h29)⟩
    simp only [List.flatMap_cons, block_append, hs₁, Option.bind_some, hs₂]

end VG.Proof.Sha3.AArch64.Scalar
