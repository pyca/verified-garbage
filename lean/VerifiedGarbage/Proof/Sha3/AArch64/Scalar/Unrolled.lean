import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lower
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core
import VerifiedGarbage.Proof.Sha3.Compl
import Mathlib.Tactic.IntervalCases
import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Boundary
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute
import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Control
import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Unrolled
import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.VectorLower
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.UnrolledLit
import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lower`. -/
section

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
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ v, v ≠ .v29 → s'.v v = s.v v) := by
  change ∀ r, s.gpr r = f.regs r at hr
  cases op with
  | spill k r => exact False.elim (hmem k r rfl)
  | reload r k => exact False.elim (hload r k rfl)
  | xor d a b =>
    refine ⟨s.write .x d (s.gpr a ^^^ s.gpr b), ?_, ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_logic, read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | move d a =>
    refine ⟨s.write .x d (s.gpr a), ?_, ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_addImm_x (by decide : 0 < 4096),
        read_x, show (BitVec.ofNat 64 0) = 0 from rfl, Size.bits, runStep_some, runBlock_nil]
      exact congrArg (fun v => some (s.write .x d v)) (BitVec.add_zero (s.gpr a))
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | ror d a n =>
    refine ⟨s.write .x d ((s.gpr a).rotateRight n), ?_, ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_ror_x hgood, read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | bic d a b =>
    refine ⟨s.write .x d (s.gpr a &&& ~~~s.gpr b), ?_, ?_, rfl, rfl, rfl, rfl,
      fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_bicRor (by decide : 0 < Size.x.bits),
        read_x, rotate_zero, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | bicRor d a b n =>
    refine ⟨s.write .x d (s.gpr a &&& ~~~(s.gpr b).rotateRight n), ?_, ?_, rfl, rfl, rfl, rfl,
      fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_bicRor (show n < Size.x.bits from hgood),
        read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | xorRor d a b n =>
    refine ⟨s.write .x d (s.gpr a ^^^ (s.gpr b).rotateRight n), ?_, ?_, rfl, rfl, rfl, rfl,
      fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_logicRor (show n < Size.x.bits from hgood),
        read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]

end VG.Proof.Sha3.AArch64.Scalar

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Round`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Reflect`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

/-- Expressions preserve the meaning of the instruction schedule without
replaying its symbolic register writes once for every output lane. -/
inductive Expr where
  | reg (r : Reg)
  | slot (k : Nat)
  | xor (a b : VG.Proof.Sha3.AArch64.Scalar.Expr)
  | bic (a b : VG.Proof.Sha3.AArch64.Scalar.Expr)
  | ror (a : VG.Proof.Sha3.AArch64.Scalar.Expr) (n : Nat)
  deriving DecidableEq

def Expr.eval (f : File) : VG.Proof.Sha3.AArch64.Scalar.Expr → Lane
  | .reg r => f.regs r
  | .slot k => f.slots k
  | .xor a b => a.eval f ^^^ b.eval f
  | .bic a b => a.eval f &&& ~~~b.eval f
  | .ror a n => (a.eval f).rotateRight n

structure SymFile where
  regs : Reg → VG.Proof.Sha3.AArch64.Scalar.Expr
  slots : Nat → VG.Proof.Sha3.AArch64.Scalar.Expr

def SymFile.write (f : VG.Proof.Sha3.AArch64.Scalar.SymFile) (r : Reg) (v : VG.Proof.Sha3.AArch64.Scalar.Expr) : VG.Proof.Sha3.AArch64.Scalar.SymFile :=
  { f with regs := fun q => if q = r then v else f.regs q }

def symStep (f : VG.Proof.Sha3.AArch64.Scalar.SymFile) : ScalarOp → VG.Proof.Sha3.AArch64.Scalar.SymFile
  | .xor d a b => f.write d (.xor (f.regs a) (f.regs b))
  | .xorRor d a b n => f.write d (.xor (f.regs a) (.ror (f.regs b) n))
  | .bic d a b => f.write d (.bic (f.regs a) (f.regs b))
  | .bicRor d a b n => f.write d (.bic (f.regs a) (.ror (f.regs b) n))
  | .ror d a n => f.write d (.ror (f.regs a) n)
  | .move d a => f.write d (f.regs a)
  | .spill k a => { f with slots := fun j => if j = k then f.regs a else f.slots j }
  | .reload d k => f.write d (f.slots k)

def symRun (ops : List ScalarOp) (f : VG.Proof.Sha3.AArch64.Scalar.SymFile) : VG.Proof.Sha3.AArch64.Scalar.SymFile := ops.foldl VG.Proof.Sha3.AArch64.Scalar.symStep f

def symInitial : VG.Proof.Sha3.AArch64.Scalar.SymFile := ⟨Expr.reg, Expr.slot⟩

def Compatible (input : File) (sf : VG.Proof.Sha3.AArch64.Scalar.SymFile) (f : File) : Prop :=
  (∀ r, f.regs r = (sf.regs r).eval input) ∧
  (∀ k, f.slots k = (sf.slots k).eval input)

theorem symStep_correct (input f : File) (sf : VG.Proof.Sha3.AArch64.Scalar.SymFile) (op : ScalarOp)
    (h : VG.Proof.Sha3.AArch64.Scalar.Compatible input sf f) : VG.Proof.Sha3.AArch64.Scalar.Compatible input (VG.Proof.Sha3.AArch64.Scalar.symStep sf op) (step f op) := by
  obtain ⟨hr, hs⟩ := h
  cases op <;> constructor <;> intro q <;>
    simp only [step, VG.Proof.Sha3.AArch64.Scalar.symStep, File.write, SymFile.write]
  all_goals first | (split <;> simp_all only [Expr.eval]) | simp_all only

theorem symRun_correct (input f : File) (sf : VG.Proof.Sha3.AArch64.Scalar.SymFile) (ops : List ScalarOp)
    (h : VG.Proof.Sha3.AArch64.Scalar.Compatible input sf f) : VG.Proof.Sha3.AArch64.Scalar.Compatible input (VG.Proof.Sha3.AArch64.Scalar.symRun ops sf) (run ops f) := by
  induction ops generalizing f sf with
  | nil => exact h
  | cons op ops ih =>
    exact ih (step f op) (VG.Proof.Sha3.AArch64.Scalar.symStep sf op) (VG.Proof.Sha3.AArch64.Scalar.symStep_correct input f sf op h)

theorem run_regs (ops : List ScalarOp) (f : File) (r : Reg) :
    (run ops f).regs r = ((VG.Proof.Sha3.AArch64.Scalar.symRun ops VG.Proof.Sha3.AArch64.Scalar.symInitial).regs r).eval f :=
  (VG.Proof.Sha3.AArch64.Scalar.symRun_correct f f VG.Proof.Sha3.AArch64.Scalar.symInitial ops ⟨fun _ => rfl, fun _ => rfl⟩).1 r

end VG.Proof.Sha3.AArch64.Scalar

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Stages`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

def Holds (reg : Nat → Reg) (A : Spec.Sha3.State) (f : File) : Prop :=
  ∀ i : Nat, (h : i < 25) → f.regs (reg i) = A[i]

def columnExpr (x : Nat) : VG.Proof.Sha3.AArch64.Scalar.Expr :=
  .xor (.xor (.xor (.xor (.reg (laneReg x)) (.reg (laneReg (x + 5))))
    (.reg (laneReg (x + 10)))) (.reg (laneReg (x + 15)))) (.reg (laneReg (x + 20)))

def thetaExpr (i : Nat) : VG.Proof.Sha3.AArch64.Scalar.Expr :=
  .xor (.reg (laneReg i)) (.xor (VG.Proof.Sha3.AArch64.Scalar.columnExpr ((i % 5 + 4) % 5))
    (.ror (VG.Proof.Sha3.AArch64.Scalar.columnExpr ((i % 5 + 1) % 5)) 63))

theorem theta_schedule : ∀ i < 25,
    (VG.Proof.Sha3.AArch64.Scalar.symRun thetaOps VG.Proof.Sha3.AArch64.Scalar.symInitial).regs (thetaReg i) = VG.Proof.Sha3.AArch64.Scalar.thetaExpr i := by decide +kernel

def rhoPiExpr (i : Nat) : VG.Proof.Sha3.AArch64.Scalar.Expr :=
  let j := Impl.Sha3.piSrc (i % 5) (i / 5)
  let k := Impl.Sha3.rhoOff j
  if k = 0 then .reg (thetaReg j) else .ror (.reg (thetaReg j)) (64 - k)

theorem rhoPi_schedule : ∀ i < 25,
    (VG.Proof.Sha3.AArch64.Scalar.symRun rhoPiOps VG.Proof.Sha3.AArch64.Scalar.symInitial).regs (laneReg i) = VG.Proof.Sha3.AArch64.Scalar.rhoPiExpr i := by decide +kernel

def chiExpr (i : Nat) : VG.Proof.Sha3.AArch64.Scalar.Expr :=
  let x := i % 5; let y := i / 5
  .xor (.reg (laneReg i))
    (.bic (.reg (laneReg ((x + 2) % 5 + 5 * y)))
      (.reg (laneReg ((x + 1) % 5 + 5 * y))))

theorem chi_schedule : ∀ i < 25,
    (VG.Proof.Sha3.AArch64.Scalar.symRun chiOps VG.Proof.Sha3.AArch64.Scalar.symInitial).regs (laneReg i) = VG.Proof.Sha3.AArch64.Scalar.chiExpr i := by decide +kernel

theorem columnExpr_eval (A : Spec.Sha3.State) (f : File) (h : VG.Proof.Sha3.AArch64.Scalar.Holds laneReg A f)
    (x : Nat) (hx : x < 5) :
    (VG.Proof.Sha3.AArch64.Scalar.columnExpr x).eval f = Proof.Sha3.C A x := by
  simp only [VG.Proof.Sha3.AArch64.Scalar.columnExpr, Expr.eval, h x (by omega), h (x + 5) (by omega),
    h (x + 10) (by omega), h (x + 15) (by omega), h (x + 20) (by omega),
    Proof.Sha3.C,
    Proof.Sha3.getElem!_eq (i := x) (hi := by omega),
    Proof.Sha3.getElem!_eq (i := x + 5) (hi := by omega),
    Proof.Sha3.getElem!_eq (i := x + 10) (hi := by omega),
    Proof.Sha3.getElem!_eq (i := x + 15) (hi := by omega),
    Proof.Sha3.getElem!_eq (i := x + 20) (hi := by omega)]

theorem theta_correct (A : Spec.Sha3.State) (f : File) (h : VG.Proof.Sha3.AArch64.Scalar.Holds laneReg A f) :
    VG.Proof.Sha3.AArch64.Scalar.Holds thetaReg (Spec.Sha3.theta A) (run thetaOps f) := by
  intro i hi
  rw [VG.Proof.Sha3.AArch64.Scalar.run_regs, VG.Proof.Sha3.AArch64.Scalar.theta_schedule i hi]
  simp only [VG.Proof.Sha3.AArch64.Scalar.thetaExpr, Expr.eval, h i hi,
    VG.Proof.Sha3.AArch64.Scalar.columnExpr_eval A f h _ (Nat.mod_lt _ (by decide)), Proof.Sha3.theta_get A hi,
    Proof.Sha3.D, BitVec.xor_comm]

theorem rhoPiExpr_eval (f : File) (i : Nat) :
    (VG.Proof.Sha3.AArch64.Scalar.rhoPiExpr i).eval f =
      Proof.Sha3.rotl (f.regs (thetaReg (Impl.Sha3.piSrc (i % 5) (i / 5))))
        (Impl.Sha3.rhoOff (Impl.Sha3.piSrc (i % 5) (i / 5))) := by
  simp only [VG.Proof.Sha3.AArch64.Scalar.rhoPiExpr, Proof.Sha3.rotl]
  split <;> simp_all only [Expr.eval]

theorem rhoPi_correct (A : Spec.Sha3.State) (f : File) (h : VG.Proof.Sha3.AArch64.Scalar.Holds thetaReg A f) :
    VG.Proof.Sha3.AArch64.Scalar.Holds laneReg (Spec.Sha3.pi (Spec.Sha3.rho A)) (run rhoPiOps f) := by
  intro i hi
  have hx : i % 5 < 5 := Nat.mod_lt _ (by decide)
  have hy : i / 5 < 5 := by omega
  have hj : Impl.Sha3.piSrc (i % 5) (i / 5) < 25 := by
    simp only [Impl.Sha3.piSrc]; omega
  rw [VG.Proof.Sha3.AArch64.Scalar.run_regs, VG.Proof.Sha3.AArch64.Scalar.rhoPi_schedule i hi, VG.Proof.Sha3.AArch64.Scalar.rhoPiExpr_eval, h _ hj,
    Proof.Sha3.rotl_eq _ (Proof.Sha3.rhoOff_lt _ hj)]
  have hp := Proof.Sha3.pi_get (Spec.Sha3.rho A) hx hy
  have hp' : (Spec.Sha3.pi (Spec.Sha3.rho A))[i] =
      (Spec.Sha3.rho A)[Impl.Sha3.piSrc (i % 5) (i / 5)] := by
    simpa only [show i % 5 + 5 * (i / 5) = i by omega] using hp
  rw [hp', Proof.Sha3.rho_get A hj]

theorem chi_correct (A : Spec.Sha3.State) (f : File) (h : VG.Proof.Sha3.AArch64.Scalar.Holds laneReg A f) :
    VG.Proof.Sha3.AArch64.Scalar.Holds laneReg (Spec.Sha3.chi A) (run chiOps f) := by
  intro i hi
  have hx : i % 5 < 5 := Nat.mod_lt _ (by decide)
  have hy : i / 5 < 5 := by omega
  have hn : (i % 5 + 1) % 5 + 5 * (i / 5) < 25 := by
    have := Nat.mod_lt (i % 5 + 1) (by decide : 0 < 5); omega
  have hn' : (i % 5 + 2) % 5 + 5 * (i / 5) < 25 := by
    have := Nat.mod_lt (i % 5 + 2) (by decide : 0 < 5); omega
  rw [VG.Proof.Sha3.AArch64.Scalar.run_regs, VG.Proof.Sha3.AArch64.Scalar.chi_schedule i hi]
  simp only [VG.Proof.Sha3.AArch64.Scalar.chiExpr, Expr.eval, h i hi, h _ hn, h _ hn']
  have hc := Proof.Sha3.chi_get A hx hy
  have hc' : (Spec.Sha3.chi A)[i] = A[i] ^^^
      (~~~A[(i % 5 + 1) % 5 + 5 * (i / 5)] &&&
        A[(i % 5 + 2) % 5 + 5 * (i / 5)]) := by
    simpa only [show i % 5 + 5 * (i / 5) = i by omega] using hc
  rw [hc', BitVec.and_comm]

end VG.Proof.Sha3.AArch64.Scalar

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.CoreExec`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

instance (op : ScalarOp) : Decidable (Good op) := by
  cases op <;> unfold Good <;> infer_instance

theorem core_good : ∀ op ∈ coreOps, Good op := by decide +kernel

theorem core_math (A : Spec.Sha3.State) (f : File) (h : VG.Proof.Sha3.AArch64.Scalar.Holds laneReg A f) :
    VG.Proof.Sha3.AArch64.Scalar.Holds laneReg (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A))))
      (run coreOps f) := by
  have hm := VG.Proof.Sha3.AArch64.Scalar.chi_correct _ _ (VG.Proof.Sha3.AArch64.Scalar.rhoPi_correct _ _ (VG.Proof.Sha3.AArch64.Scalar.theta_correct A f h))
  simpa only [coreOps, run, List.foldl_append] using hm

end VG.Proof.Sha3.AArch64.Scalar

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Round`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

def iotaFile (f : File) (rc : Lane) : File :=
  f.write .x0 (f.regs .x0 ^^^ rc)

theorem laneReg_zero : ∀ i < 25, laneReg i = .x0 ↔ i = 0 := by decide +kernel

theorem iota_correct (A : Spec.Sha3.State) (f : File) (h : VG.Proof.Sha3.AArch64.Scalar.Holds laneReg A f)
    (ir : Nat) : VG.Proof.Sha3.AArch64.Scalar.Holds laneReg (Spec.Sha3.iota A ir) (VG.Proof.Sha3.AArch64.Scalar.iotaFile f (Spec.Sha3.RC ir)) := by
  intro i hi
  by_cases hz : i = 0
  · subst i
    simp only [VG.Proof.Sha3.AArch64.Scalar.iotaFile, File.write, laneReg, ↓reduceIte, Spec.Sha3.iota,
      Vector.getElem_set_self]
    exact congrArg (· ^^^ Spec.Sha3.RC ir) (h 0 (by decide))
  · have hr : laneReg i ≠ .x0 := by
      intro hr; exact hz ((VG.Proof.Sha3.AArch64.Scalar.laneReg_zero i hi).mp hr)
    simp only [VG.Proof.Sha3.AArch64.Scalar.iotaFile, File.write, hr, ↓reduceIte, h i hi, Spec.Sha3.iota,
      Vector.getElem_set, Ne.symm hz]

@[irreducible] def roundFile (f : File) (rc : Lane) : File :=
  VG.Proof.Sha3.AArch64.Scalar.iotaFile (run chiOps (run rhoPiOps (run thetaOps f))) rc

theorem round_correct (A : Spec.Sha3.State) (f : File) (h : VG.Proof.Sha3.AArch64.Scalar.Holds laneReg A f)
    (ir : Nat) : VG.Proof.Sha3.AArch64.Scalar.Holds laneReg (Spec.Sha3.rnd A ir) (VG.Proof.Sha3.AArch64.Scalar.roundFile f (Spec.Sha3.RC ir)) := by
  unfold VG.Proof.Sha3.AArch64.Scalar.roundFile
  exact VG.Proof.Sha3.AArch64.Scalar.iota_correct _ _ (VG.Proof.Sha3.AArch64.Scalar.chi_correct _ _ (VG.Proof.Sha3.AArch64.Scalar.rhoPi_correct _ _ (VG.Proof.Sha3.AArch64.Scalar.theta_correct A f h))) ir

theorem rounds_correct (irs : List Nat) (A : Spec.Sha3.State) (f : File)
    (h : VG.Proof.Sha3.AArch64.Scalar.Holds laneReg A f) :
    VG.Proof.Sha3.AArch64.Scalar.Holds laneReg (irs.foldl Spec.Sha3.rnd A)
      (irs.foldl (fun f ir => VG.Proof.Sha3.AArch64.Scalar.roundFile f (Spec.Sha3.RC ir)) f) := by
  induction irs generalizing A f with
  | nil => exact h
  | cons ir irs ih =>
    simp only [List.foldl_cons]
    have hn := VG.Proof.Sha3.AArch64.Scalar.round_correct A f h ir
    exact ih (Spec.Sha3.rnd A ir) (VG.Proof.Sha3.AArch64.Scalar.roundFile f (Spec.Sha3.RC ir)) hn

theorem keccakF_correct (A : Spec.Sha3.State) (f : File) (h : VG.Proof.Sha3.AArch64.Scalar.Holds laneReg A f) :
    VG.Proof.Sha3.AArch64.Scalar.Holds laneReg (Spec.Sha3.keccakF A)
      ((List.range 24).foldl (fun f ir => VG.Proof.Sha3.AArch64.Scalar.roundFile f (Spec.Sha3.RC ir)) f) :=
  VG.Proof.Sha3.AArch64.Scalar.rounds_correct (List.range 24) A f h

end VG.Proof.Sha3.AArch64.Scalar

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

structure VectorFileRel (f : File) (s : VG.AArch64.State) : Prop where
  regs : ∀ r, s.gpr r = f.regs r
  slots : ∀ k < 2, vdword (s.v (slotV k)) 0 = f.slots k

private theorem slotV_eq {j k : Nat} (hj : j < 2) (hk : k < 2) :
    slotV j = slotV k ↔ j = k := by
  interval_cases j <;> interval_cases k <;> decide

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
    · simp only [lowerVector, runBlock_cons, exec, VOp.eval, Option.map_some, runStep_some, runBlock_nil]
    · intro r; exact hr.regs r
    · intro j hj
      simp only [step, RegUpd.v_setV]
      by_cases he : j = k
      · subst j
        simp only [ite_true, vdword_ofVDwords_0, hr.regs]
      · simp only [ite_eq_right he, ite_eq_right ((slotV_eq hj hk).not.mpr he), hr.slots j hj]
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
    refine ⟨s', hs, ⟨hregs, ?_⟩, hm, hrd, hwr, hsp, fun v _ _ _ h29 => hv v h29⟩
    · intro k hk
      rw [hv (slotV k) (by unfold slotV tempSlotV; split <;> decide)]
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

/-- The vector-slot core has the same lane semantics and writes no memory. -/
theorem vector_core_ok (A : Spec.Sha3.State) (s : VG.AArch64.State)
    (hl : ∀ i : Nat, (hi : i < 25) → s.gpr (laneReg i) = A[i]) :
    ∃ s', runBlock isa vectorCoreInstrs s = some s' ∧
      (∀ i : Nat, (hi : i < 25) → s'.gpr (laneReg i) =
        (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A))))[i]) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → s'.v v = s.v v) := by
  let f : File := ⟨s.gpr, fun k => vdword (s.v (slotV k)) 0⟩
  have hr : VectorFileRel f s := ⟨fun _ => rfl, fun _ _ => rfl⟩
  have hmath := core_math A f hl
  obtain ⟨s', hs, hr', hm, hrd, hwr, hsp, hv⟩ := vector_list_ok coreOps core_good f s hr
  exact ⟨s', hs, fun i hi => (hr'.regs (laneReg i)).trans (hmath i hi), hm, hrd, hwr, hsp, hv⟩

end VG.Proof.Sha3.AArch64.Scalar

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Unrolled`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure Keep (s s' : VG.AArch64.State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.refl (s : VG.AArch64.State) : VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep s s := ⟨rfl,rfl,rfl⟩
theorem Keep.trans {s t u : VG.AArch64.State} (h : VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep s t) (k : VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep t u) : VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep s u :=
  ⟨k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩

def SavedVector (orig s : VG.AArch64.State) : Prop :=
  ∀ i < 11, vdword (s.v (savedVec i)) 0 = orig.gpr (savedReg i)

theorem savedVec_inj : ∀ i < 11, ∀ j < 11, savedVec i = savedVec j ↔ i = j := by decide

theorem savedVec_ne_ptrs : ∀ i < 11, savedVec i ≠ .v30 ∧ savedVec i ≠ .v31 := by decide

theorem savedVec_not_preserved : ∀ i < 11, ∀ r ∈ preservedV, r ≠ savedVec i := by decide

def Ptrs (s₀ s : VG.AArch64.State) : Prop :=
  vdword (s.v .v30) 0 = s₀.gpr .x0 ∧ vdword (s.v .v31) 0 = s₀.gpr .x1

def Lanes (s : VG.AArch64.State) (A : Spec.Sha3.State) : Prop :=
  ∀ i (hi : i < 25), s.gpr (laneReg i) = A[i]

theorem laneReg_inj : ∀ i < 25, ∀ j < 25, laneReg i = laneReg j ↔ i = j := by decide

theorem savedReg_inj : ∀ i < 11, ∀ j < 11, savedReg i = savedReg j ↔ i = j := by decide

theorem laneReg_ne_x30 : ∀ i < 25, laneReg i ≠ .x30 := by decide

end VG.Proof.Sha3.AArch64.Scalar.Boundary

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Control`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar.Control
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Control
open VG.Proof.Sha3.AArch64

structure ConstantKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x26 → s'.gpr r = s.gpr r
  vec : s'.v = s.v
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem constant_ok (v : BitVec 64) (s : State) :
    WP isa (.block (constant v)) s fun s' =>
      VG.Proof.Sha3.AArch64.Scalar.Control.ConstantKeep s s' ∧ s'.gpr .x26 = Sha3.Vector.constantLow v := by
  by_cases h1 : v.extractLsb' 16 16 = 0 <;>
    by_cases h2 : v.extractLsb' 32 16 = 0 <;>
    by_cases h3 : v.extractLsb' 48 16 = 0
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

end VG.Proof.Sha3.AArch64.Scalar.Control

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Load`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure LoadInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep s₀ s
  mem : s.mem = s₀.mem
  vec : s.v = s₀.v
  base : s.gpr .x30 = s₀.gpr .x0
  lanes : ∀ j < k, s.gpr (laneReg j) =
    s₀.mem.readW (s₀.gpr .x0 + BitVec.ofNat 64 (8*j)) 64

theorem load_ok (s₀ : VG.AArch64.State)
    (hin : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr)
      (s₀.gpr .x0 + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block load) s₀ fun s' => VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep s₀ s' ∧ s'.mem = s₀.mem ∧ s'.v = s₀.v ∧
      VG.Proof.Sha3.AArch64.Scalar.Boundary.Lanes s' (Spec.Sha3.stateAt s₀.mem (s₀.gpr .x0)) := by
  have hrun : ∀ s, VG.Proof.Sha3.AArch64.Scalar.Boundary.LoadInv s₀ 0 s →
      WP isa (.block ((List.range 25).map fun i => .ldr .x (laneReg i) .x30 (8*i)))
        s (VG.Proof.Sha3.AArch64.Scalar.Boundary.LoadInv s₀ 25) := by
    intro s hs
    rw [show (List.range 25).map (fun i => Instr.ldr .x (laneReg i) .x30 (8*i)) =
      (List.range 25).flatMap (fun i => [Instr.ldr .x (laneReg i) .x30 (8*i)]) by rfl]
    refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.AArch64.Scalar.Boundary.LoadInv s₀) (fun i s hi hs => ?_)
      25 (Nat.le_refl _) s hs
    refine WP.cons (exec_ldr_x ⟨by omega,by omega⟩ ?_) (wp_nil ?_)
    · rw [hs.keep.rd,hs.keep.wr,hs.base]
      exact hin i hi
    · refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.mem,hs.vec,?_,fun j hj => ?_⟩
      · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
          Ne.symm (VG.Proof.Sha3.AArch64.Scalar.Boundary.laneReg_ne_x30 i hi),ite_false,hs.base]
      · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
          VG.Proof.Sha3.AArch64.Scalar.Boundary.laneReg_inj j (by omega) i hi]
        split
        · rename_i he; subst j
          rw [hs.mem,hs.base]
        · exact hs.lanes j (by omega)
  unfold load
  refine WP.cons (exec_addImm_x (by decide)) ?_
  refine (hrun _ ?_).mono fun s hs => ⟨hs.keep,hs.mem,hs.vec,?_⟩
  · refine ⟨⟨rfl,rfl,rfl⟩,rfl,rfl,?_,fun _ h => absurd h (by omega)⟩
    simp only [RegUpd.gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq,
      show BitVec.ofNat 64 0 = 0 by rfl]
    exact BitVec.add_zero _
  · intro i hi
    simpa only [Spec.Sha3.stateAt,Vector.getElem_ofFn,VG.Proof.Sha3.laneAddr] using hs.lanes i hi

end VG.Proof.Sha3.AArch64.Scalar.Boundary

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Restore`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure RestoreInv (orig start : State) (k : Nat) (s : State) : Prop where
  keep : VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep start s
  mem : s.mem = start.mem
  vec : s.v = start.v
  vals : ∀ i < k, s.gpr (savedReg i) = orig.gpr (savedReg i)

theorem restore_ok (orig start : State) (hsave : VG.Proof.Sha3.AArch64.Scalar.Boundary.SavedVector orig start) :
    WP isa (.block restore) start fun s => VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep start s ∧ s.mem = start.mem ∧ s.v = start.v ∧
      ∀ r ∈ preserved, s.gpr r = orig.gpr r := by
  unfold restore
  rw [show (List.range 11).map (fun i => Instr.umov .x (savedReg i) (savedVec i) 0) =
    (List.range 11).flatMap (fun i => [Instr.umov .x (savedReg i) (savedVec i) 0]) by rfl]
  refine (wp_range_flatMap (M := isa) (VG.Proof.Sha3.AArch64.Scalar.Boundary.RestoreInv orig start) (fun i s hi hs => ?_)
    11 (Nat.le_refl _) start ⟨Keep.refl _,rfl,rfl,fun _ h => by omega⟩).mono
    fun s hs => ⟨hs.keep,hs.mem,hs.vec,fun r hr => ?_⟩
  · refine WP.cons (exec_umov_low s (savedReg i) (savedVec i)) (wp_nil ?_)
    refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.mem,hs.vec,fun j hj => ?_⟩
    simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,VG.Proof.Sha3.AArch64.Scalar.Boundary.savedReg_inj j (by omega) i hi]
    split
    · rename_i h; subst j
      rw [hs.vec]
      exact hsave i hi
    · exact hs.vals j (by omega)
  · have hall : ∀ r ∈ preserved, ∃ i : Fin 11, r = savedReg i.val := by decide
    obtain ⟨i,rfl⟩ := hall r hr
    exact hs.vals i.val i.isLt
end VG.Proof.Sha3.AArch64.Scalar.Boundary

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Save`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure SaveInv (orig : State) (k : Nat) (s : State) : Prop where
  keep : VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep orig s
  gpr : s.gpr = orig.gpr
  mem : s.mem = orig.mem
  vals : ∀ i < k, vdword (s.v (savedVec i)) 0 = orig.gpr (savedReg i)
  vec : ∀ r ∈ preservedV, s.v r = orig.v r

theorem save_vectors_ok (orig : State) :
    WP isa (.block ((List.range 11).map fun i => .vop (.dup .d2 (savedVec i) (savedReg i))))
      orig (VG.Proof.Sha3.AArch64.Scalar.Boundary.SaveInv orig 11) := by
  rw [show (List.range 11).map (fun i => Instr.vop (.dup .d2 (savedVec i) (savedReg i))) =
    (List.range 11).flatMap (fun i => [Instr.vop (.dup .d2 (savedVec i) (savedReg i))]) by rfl]
  refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.AArch64.Scalar.Boundary.SaveInv orig) (fun i s hi hs => ?_)
    11 (Nat.le_refl _) orig ⟨Keep.refl _,rfl,rfl,fun _ h => by omega,fun _ _ => rfl⟩
  refine WP.cons rfl (wp_nil ?_)
  refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.gpr,hs.mem,fun j hj => ?_,fun r hr => ?_⟩
  · simp only [RegUpd.v_setV,VG.Proof.Sha3.AArch64.Scalar.Boundary.savedVec_inj j (by omega) i hi]
    split
    · rename_i h; subst j
      simp only [vdword_ofVDwords_0,hs.gpr]
    · exact hs.vals j (by omega)
  · simp only [RegUpd.v_setV,VG.Proof.Sha3.AArch64.Scalar.Boundary.savedVec_not_preserved i hi r hr,ite_false]
    exact hs.vec r hr

theorem save_ok (orig : State) :
    WP isa (.block save) orig fun s => VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep orig s ∧ s.gpr = orig.gpr ∧
      s.mem = orig.mem ∧ VG.Proof.Sha3.AArch64.Scalar.Boundary.SavedVector orig s ∧ VG.Proof.Sha3.AArch64.Scalar.Boundary.Ptrs orig s ∧
      (∀ r ∈ preservedV, s.v r = orig.v r) := by
  unfold save
  rw [WP.block_append_iff]
  refine (VG.Proof.Sha3.AArch64.Scalar.Boundary.save_vectors_ok orig).mono fun s hs => ?_
  refine WP.cons rfl (WP.cons rfl (wp_nil ?_))
  refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.gpr,hs.mem,?_,?_,?_⟩
  · intro i hi
    have hn := VG.Proof.Sha3.AArch64.Scalar.Boundary.savedVec_ne_ptrs i hi
    simp only [RegUpd.v_setV,hn.1,hn.2,ite_false]
    exact hs.vals i hi
  · simp only [VG.Proof.Sha3.AArch64.Scalar.Boundary.Ptrs,RegUpd.v_setV,reduceCtorEq,ite_false,ite_true,
      vdword_ofVDwords_0,RegUpd.gpr_setV,hs.gpr]
    exact ⟨True.intro,True.intro⟩
  · intro r hr
    have hn : ∀ r ∈ preservedV, r ≠ .v30 ∧ r ≠ .v31 := by decide
    simp only [RegUpd.v_setV,(hn r hr).1,(hn r hr).2,ite_false]
    exact hs.vec r hr
end VG.Proof.Sha3.AArch64.Scalar.Boundary

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

theorem laneReg_injective : ∀ i < 25, ∀ j < 25,
    VG.Impl.Sha3.AArch64.Scalar.laneReg i = VG.Impl.Sha3.AArch64.Scalar.laneReg j → i = j := by decide +kernel

theorem thetaReg_injective : ∀ i < 25, ∀ j < 25,
    thetaReg i = thetaReg j → i = j := by decide +kernel

theorem scratch_not_lane : ∀ r ∈ [Reg.x26, .x27, .x28, .x30],
    ∀ i < 25, VG.Impl.Sha3.AArch64.Scalar.laneReg i ≠ r := by decide +kernel

/-- These operand constraints allow a baseline-ISA implementation of BIC
as AND then XOR, and EOR-with-rotation without destroying a live source. -/
def BaselineSafe : ScalarOp → Prop
  | .bic d a _ => d ≠ a
  | .bicRor d a b _ => d ≠ a ∧ d ≠ b
  | .xorRor d a b _ => a ≠ b ∧ d ≠ b
  | .spill k _ => k < 2
  | .reload _ k => k < 2
  | _ => True

instance (op : ScalarOp) : Decidable (VG.Proof.Sha3.AArch64.Scalar.BaselineSafe op) := by
  cases op <;> unfold VG.Proof.Sha3.AArch64.Scalar.BaselineSafe <;> infer_instance

theorem baseline_safe : ∀ op ∈ thetaOps ++ rhoPiOps ++ chiOps,
    VG.Proof.Sha3.AArch64.Scalar.BaselineSafe op := by decide +kernel

end VG.Proof.Sha3.AArch64.Scalar

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Store`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure StoreInv (s₀ : VG.AArch64.State) (p : Addr) (A : Spec.Sha3.State)
    (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep s₀ s
  gpr : s.gpr = s₀.gpr
  vec : s.v = s₀.v
  frame : Frame [⟨p,200⟩] s₀.mem s.mem
  vals : ∀ i (_hi : i < k) (h25 : i < 25), s.mem.readW (p + BitVec.ofNat 64 (8*i)) 64 = A[i]

theorem store_words_ok (s₀ : VG.AArch64.State) (A : Spec.Sha3.State)
    (hA : VG.Proof.Sha3.AArch64.Scalar.Boundary.Lanes s₀ A)
    (hin : ∀ i < 25, InRegions s₀.wr (s₀.gpr .x30 + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block ((List.range 25).map fun i => .str .x (laneReg i) .x30 (8*i)))
      s₀ (VG.Proof.Sha3.AArch64.Scalar.Boundary.StoreInv s₀ (s₀.gpr .x30) A 25) := by
  rw [show (List.range 25).map (fun i => Instr.str .x (laneReg i) .x30 (8*i)) =
    (List.range 25).flatMap (fun i => [Instr.str .x (laneReg i) .x30 (8*i)]) by rfl]
  refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.AArch64.Scalar.Boundary.StoreInv s₀ (s₀.gpr .x30) A) (fun i s hi hs => ?_)
    25 (Nat.le_refl _) s₀ ⟨Keep.refl _,rfl,rfl,Frame.refl _ _,fun _ h => absurd h (by omega)⟩
  refine WP.cons (exec_str_x ⟨by omega,by omega⟩ ?_) (wp_nil ?_)
  · rw [hs.keep.wr,hs.gpr]
    exact hin i hi
  · refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.gpr,hs.vec,?_,fun j hj h25 => ?_⟩
    · change Frame _ _ (s.mem.writeW _ _)
      rw [hs.gpr]
      exact hs.frame.writeW (r := ⟨s₀.gpr .x30,200⟩) (by simp) _ (Offset.contains_base _ (by omega) (by omega))
    · change (s.mem.writeW _ _).readW _ 64 = _
      rw [hs.gpr]
      by_cases he : j = i
      · subst j
        rw [Mem.readW_writeW_self64]
        exact hA i hi
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact hs.vals j (by omega) h25

theorem store_ok (s₀ : VG.AArch64.State) (p : Addr) (A : Spec.Sha3.State)
    (hA : VG.Proof.Sha3.AArch64.Scalar.Boundary.Lanes s₀ A) (hptr : vdword (s₀.v .v30) 0 = p)
    (hin : ∀ i < 25, InRegions s₀.wr (p + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block store) s₀ fun s' => VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep s₀ s' ∧ s'.v = s₀.v ∧
      Frame [⟨p,200⟩] s₀.mem s'.mem ∧ Spec.Sha3.stateAt s'.mem p = A := by
  change (s₀.v .v30).extractLsb' (64*0) 64 = p at hptr
  unfold store
  refine WP.cons rfl ?_
  refine (VG.Proof.Sha3.AArch64.Scalar.Boundary.store_words_ok _ A ?_ ?_).mono fun s hs => ?_
  · intro i hi
    simpa only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,VG.Proof.Sha3.AArch64.Scalar.Boundary.laneReg_ne_x30 i hi,ite_false]
      using hA i hi
  · intro i hi
    simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq,RegUpd.wr_write,hptr] using hin i hi
  · have hb : (s₀.write .x .x30 ((s₀.v .v30).extractLsb' (64*0) 64)).gpr .x30 = p := by
      simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq,vdword] using hptr
    refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.vec,?_,?_⟩
    · simpa only [hb,RegUpd.mem_write] using hs.frame
    · apply Vector.ext
      intro i hi
      simpa only [Spec.Sha3.stateAt,Vector.getElem_ofFn,VG.Proof.Sha3.laneAddr,hb]
        using hs.vals i hi hi

end VG.Proof.Sha3.AArch64.Scalar.Boundary

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Wrap`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

/-- The middle may use every GPR but must retain public pointers, saved GPRs,
and the ABI-protected vector registers. -/
structure CoreState (orig : VG.AArch64.State) (A : Spec.Sha3.State) (s : VG.AArch64.State) : Prop where
  keep : VG.Proof.Sha3.AArch64.Scalar.Boundary.Keep orig s
  ptrs : VG.Proof.Sha3.AArch64.Scalar.Boundary.Ptrs orig s
  saved : VG.Proof.Sha3.AArch64.Scalar.Boundary.SavedVector orig s
  vec : ∀ r ∈ preservedV, s.v r = orig.v r
  lanes : VG.Proof.Sha3.AArch64.Scalar.Boundary.Lanes s A

theorem wrap_correct (middle : Prog isa)
    (hmid : ∀ orig A s, VG.Proof.Sha3.AArch64.Pre orig → VG.Proof.Sha3.AArch64.Scalar.Boundary.CoreState orig A s →
      WP isa middle s (VG.Proof.Sha3.AArch64.Scalar.Boundary.CoreState orig (Spec.Sha3.keccakF A)))
    (orig : VG.AArch64.State) (hp : VG.Proof.Sha3.AArch64.Pre orig) :
    WP isa (wrap middle) orig fun s' => abiPreserved orig s' ∧
      VG.Proof.Sha3.permuteAArch64.post orig s' := by
  unfold wrap
  rw [WP.seq_iff]
  refine (VG.Proof.Sha3.AArch64.Scalar.Boundary.save_ok orig).mono fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  refine (VG.Proof.Sha3.AArch64.Scalar.Boundary.load_ok s₁ (fun i hi => ?_)).mono fun s₂ h₂ => ?_
  · rw [h₁.1.rd,h₁.1.wr,h₁.2.1]
    exact hp.in_all (hp.lane_in (.inl rfl) hi)
  · have ha : VG.Proof.Sha3.AArch64.Scalar.Boundary.Lanes s₂ (Spec.Sha3.stateAt orig.mem (orig.gpr .x0)) := by
      have hst : Spec.Sha3.stateAt s₁.mem (s₁.gpr .x0) =
          Spec.Sha3.stateAt orig.mem (orig.gpr .x0) := by rw [h₁.2.1, h₁.2.2.1]
      rw [hst] at h₂
      exact h₂.2.2.2
    have hs₂ : VG.Proof.Sha3.AArch64.Scalar.Boundary.CoreState orig (Spec.Sha3.stateAt orig.mem (orig.gpr .x0)) s₂ := by
      refine ⟨h₁.1.trans h₂.1,?_,?_,?_,ha⟩
      · simpa only [VG.Proof.Sha3.AArch64.Scalar.Boundary.Ptrs,h₂.2.2.1] using h₁.2.2.2.2.1
      · simpa only [VG.Proof.Sha3.AArch64.Scalar.Boundary.SavedVector,h₂.2.2.1] using h₁.2.2.2.1
      · intro r hr
        rw [h₂.2.2.1]
        exact h₁.2.2.2.2.2 r hr
    rw [WP.seq_iff]
    refine (hmid orig _ s₂ hp hs₂).mono fun s₃ h₃ => ?_
    rw [WP.seq_iff]
    refine (VG.Proof.Sha3.AArch64.Scalar.Boundary.store_ok s₃ (orig.gpr .x0) _ h₃.lanes h₃.ptrs.1 (fun i hi => ?_)).mono
      fun s₄ h₄ => ?_
    · rw [h₃.keep.wr]
      exact hp.lane_in (.inl rfl) hi
    · have hs₄ : VG.Proof.Sha3.AArch64.Scalar.Boundary.SavedVector orig s₄ := by
        simpa only [VG.Proof.Sha3.AArch64.Scalar.Boundary.SavedVector,h₄.2.1] using h₃.saved
      refine (VG.Proof.Sha3.AArch64.Scalar.Boundary.restore_ok orig s₄ hs₄).mono fun s' h₅ => ?_
      refine ⟨⟨h₅.2.2.2,h₅.1.sp.trans (h₄.1.sp.trans h₃.keep.sp),?_⟩,?_⟩
      · intro r hr
        rw [h₅.2.2.1,h₄.2.1,h₃.vec r hr]
      · change Spec.Sha3.stateAt s'.mem (orig.gpr .x0) = _
        rw [h₅.2.1]
        exact h₄.2.2.2

end VG.Proof.Sha3.AArch64.Scalar.Boundary

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Unrolled`. -/
section

/-!
# The unrolled scalar permutation: correctness

Each unrolled round is the vector-slot core (`vector_core_ok`), the round
constant built from immediates (`Control.constant_ok`) and its XOR into lane
0; together they keep `Boundary.CoreState`, the middle's contract in
`wrap_correct`.
-/

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Proof.Sha3.AArch64.Scalar.Boundary

theorem savedVec_not_temps : ∀ i < 11, Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v24 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v25 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v28 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v29 := by decide

theorem preservedV_not_temps : ∀ r ∈ preservedV, r ≠ .v24 ∧ r ≠ .v25 ∧ r ≠ .v28 ∧ r ≠ .v29 := by
  decide

/-- What the rounds keep besides the boundary's invariant: memory, and the
AdvSIMD registers other than the core's temporaries. -/
structure RoundKeep (s t : State) : Prop where
  mem : t.mem = s.mem
  v : ∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → t.v v = s.v v

theorem RoundKeep.refl (s : State) : VG.Proof.Sha3.AArch64.Scalar.RoundKeep s s := ⟨rfl, fun _ _ _ _ _ => rfl⟩

theorem RoundKeep.trans {s t u : State} (h : VG.Proof.Sha3.AArch64.Scalar.RoundKeep s t) (k : VG.Proof.Sha3.AArch64.Scalar.RoundKeep t u) : VG.Proof.Sha3.AArch64.Scalar.RoundKeep s u :=
  ⟨k.mem.trans h.mem, fun v a b c d => (k.v v a b c d).trans (h.v v a b c d)⟩

/-- One unrolled round computes `Rnd` and keeps the boundary's invariant. -/
theorem unrolled_round_ok (orig : State) (A : Spec.Sha3.State) (r : Nat) (hr : r < 24)
    (s : State) (hs : VG.Proof.Sha3.AArch64.Scalar.Boundary.CoreState orig A s) :
    WP isa (.block (unrolledRound r)) s fun t =>
      VG.Proof.Sha3.AArch64.Scalar.Boundary.CoreState orig (Spec.Sha3.rnd A r) t ∧ VG.Proof.Sha3.AArch64.Scalar.RoundKeep s t := by
  obtain ⟨t, ht, hl, hm, hrd, hwr, hsp, hv⟩ := vector_core_ok A s hs.lanes
  unfold unrolledRound
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨t, ht, ?_⟩
  rw [WP.block_append_iff]
  refine (Control.constant_ok (Spec.Sha3.RC r) t).mono fun u ⟨hk, hu⟩ => ?_
  rw [Sha3.Vector.constantLow_RC r hr] at hu
  refine WP.cons rfl (wp_nil ?_)
  have hvu : ∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → u.v v = s.v v :=
    fun v h24 h25 h28 h29 => (congrFun hk.vec v).trans (hv v h24 h25 h28 h29)
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ⟨hk.mem.trans hm, fun v a b c d => by
    rw [RegUpd.v_write]; exact hvu v a b c d⟩⟩
  · exact (hk.rd.trans hrd).trans hs.keep.rd
  · exact (hk.wr.trans hwr).trans hs.keep.wr
  · exact (hk.sp.trans hsp).trans hs.keep.sp
  · simp only [VG.Proof.Sha3.AArch64.Scalar.Boundary.Ptrs, RegUpd.v_write]
    rw [hvu .v30 (by decide) (by decide) (by decide) (by decide),
      hvu .v31 (by decide) (by decide) (by decide) (by decide)]
    exact hs.ptrs
  · intro i hi
    have hn := VG.Proof.Sha3.AArch64.Scalar.savedVec_not_temps i hi
    change vdword ((u.write .x .x0 _).v _) 0 = _
    rw [RegUpd.v_write, hvu _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact hs.saved i hi
  · intro q hq
    have hn := VG.Proof.Sha3.AArch64.Scalar.preservedV_not_temps q hq
    rw [RegUpd.v_write, hvu q hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact hs.vec q hq
  · intro i hi
    have h26 := VG.Proof.Sha3.AArch64.Scalar.scratch_not_lane .x26 (by simp) i hi
    have h0 : u.gpr .x0 = (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A))))[0] :=
      (hk.gpr .x0 (by decide)).trans (hl 0 (by decide))
    simp only [RegUpd.gpr_write, State.read, Size.bits, BitVec.setWidth_eq]
    by_cases hz : i = 0
    · subst i
      simp only [Impl.Sha3.AArch64.Scalar.laneReg, ite_true, h0, hu, Spec.Sha3.rnd, Spec.Sha3.iota,
        Vector.getElem_set_self]
    · have hr0 : Impl.Sha3.AArch64.Scalar.laneReg i ≠ .x0 := by
        intro he; exact hz ((laneReg_zero i hi).mp he)
      simp only [hr0, ite_false, hk.gpr _ h26, hl i hi, Spec.Sha3.rnd, Spec.Sha3.iota,
        Vector.getElem_set, Ne.symm hz]

theorem unrolled_rounds_list_ok (rs : List Nat) (hrs : ∀ r ∈ rs, r < 24)
    (orig : State) (A : Spec.Sha3.State) (s : State) (hs : VG.Proof.Sha3.AArch64.Scalar.Boundary.CoreState orig A s) :
    WP isa (.block (rs.flatMap unrolledRound)) s fun t =>
      VG.Proof.Sha3.AArch64.Scalar.Boundary.CoreState orig (rs.foldl Spec.Sha3.rnd A) t ∧ VG.Proof.Sha3.AArch64.Scalar.RoundKeep s t := by
  induction rs generalizing A s with
  | nil => exact wp_nil ⟨hs, RoundKeep.refl s⟩
  | cons r rs ih =>
    rw [List.flatMap_cons, List.foldl_cons, WP.block_append_iff]
    exact (VG.Proof.Sha3.AArch64.Scalar.unrolled_round_ok orig A r (hrs r (by simp)) s hs).mono fun t ht =>
      (ih (fun q hq => hrs q (by simp only [List.mem_cons]; exact Or.inr hq)) _ t ht.1).mono
        fun u hu => ⟨hu.1, ht.2.trans hu.2⟩

theorem unrolled_rounds_ok (orig : State) (A : Spec.Sha3.State) (s : State)
    (hs : VG.Proof.Sha3.AArch64.Scalar.Boundary.CoreState orig A s) :
    WP isa (.block unrolledRounds) s fun t =>
      VG.Proof.Sha3.AArch64.Scalar.Boundary.CoreState orig (Spec.Sha3.keccakF A) t ∧ VG.Proof.Sha3.AArch64.Scalar.RoundKeep s t :=
  VG.Proof.Sha3.AArch64.Scalar.unrolled_rounds_list_ok (List.range 24) (fun _ h => List.mem_range.mp h) orig A s hs

/-- The unrolled permutation has the public permutation contract. -/
theorem unrolled_permute_correct (s : State) (hs : VG.Proof.Sha3.permuteAArch64.pre s) :
    ∃ t s', Exec isa unrolledPermute s t s' ∧ abiPreserved s s' ∧
      VG.Proof.Sha3.permuteAArch64.post s s' :=
  Boundary.wrap_correct (.block unrolledRounds) (fun orig A s _ hs => (VG.Proof.Sha3.AArch64.Scalar.unrolled_rounds_ok orig A s hs).mono fun _ h => h.1)
    s (VG.Proof.Sha3.AArch64.pre_of s hs)

theorem unrolled_permute_noCalls : unrolledPermute.noCalls = true := by lit_decide
theorem unrolled_permute_noFrames : unrolledPermute.noFrames = true := by lit_decide

theorem unrolled_permute_ct : ConstantTime isa VG.Proof.Sha3.permuteAArch64.pre
    VG.Proof.Sha3.permuteAArch64.pub unrolledPermute := by
  refine VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨⟨hsp, fun r hr => ?_⟩, ?_⟩
  · simp only [VectorTaint.ofRegs, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · intro r hr
    simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hr

theorem unrolled_permute_verified :
    Verified AArch64.target unrolledPermute (Spec.Sha3.permuteContract AArch64.abi) :=
  Verified.of_correct VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_correct VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_ct (by
    sig_implies [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, VG.Proof.Sha3.permuteAArch64,
      AArch64.abi, AArch64.argRegs] [VG.Proof.Sha3.AArch64.satState]
      using VG.Proof.Sha3.AArch64.satState)

#assert_standard_axioms VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_correct
#assert_standard_axioms VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_ct
#assert_standard_axioms VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_verified

end VG.Proof.Sha3.AArch64.Scalar

end

end
