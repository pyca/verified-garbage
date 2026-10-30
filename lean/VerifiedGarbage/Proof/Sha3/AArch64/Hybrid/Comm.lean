module

public import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.TCB.AArch64.Isa
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-!
# AArch64: vector-only and scalar-only instructions commute

The instructions of a two-state SHA-3 round read and write only vector
registers (`vecOnly`); those of a scalar Keccak round read and write only
general registers and memory, through the stack pointer for its spills
(`scalarOnly`). Any two such instructions commute (`comm`), so any
interleaving of the two rounds runs as one round and then the other
(`indeps`, with `VG.Interleave.run_merge`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Hybrid
open VG VG.AArch64

/-- The vector operations that read and write only vector registers. -/
def vopVecOnly : VOp → Bool
  | .logic .. | .eor3 .. | .bcax .. | .rax1 .. | .xar .. => true
  | _ => false

def vecOnly : Instr → Bool
  | .vop op => vopVecOnly op
  | _ => false

/-- The scalar instructions of the class: general registers, flags left
alone, memory only at the stack pointer. -/
def scalarOnly : Instr → Bool
  | .logic .. | .logicRor .. | .bicRor .. | .ror .. | .addImm .. | .movz .. | .movk ..
  | .ldrSp .. | .strSp .. => true
  | _ => false

theorem VOp.eval_congr {op : VOp} (h : vopVecOnly op = true) {s t : State} (hv : s.v = t.v) :
    op.eval s = op.eval t := by
  cases op <;> simp only [vopVecOnly, reduceCtorEq] at h <;> simp only [reduceVOpEval, hv]

theorem exec_setV {y : Instr} (h : scalarOnly y = true) (s : State) (d : VReg) (x : BitVec 128) :
    exec y (s.setV d x) = (exec y s).map (·.setV d x) := by
  cases y <;> simp only [scalarOnly, reduceCtorEq] at h
  case ldrSp t off =>
    simp only [reduceExec, State.load]
    by_cases ho : off % 8 = 0 ∧ off < 32768
    · by_cases hi : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8
      · simp only [ho, hi, and_self, ite_true, Option.map_some, State.setV, State.write]
      · simp [ho, hi, State.setV]
    · simp only [ho, ite_false, Option.map_none]
  case strSp t off =>
    simp only [reduceExec, State.store]
    by_cases ho : off % 8 = 0 ∧ off < 32768
    · by_cases hi : InRegions s.wr (s.sp + BitVec.ofNat 64 off) 8
      · simp only [ho, hi, and_self, ite_true, Option.map_some, State.setV, State.read]
      · simp [ho, hi, State.setV]
    · simp only [ho, ite_false, Option.map_none]
  all_goals
    simp only [reduceExec]
    first
    | (split <;> simp only [Option.map_some, Option.map_none, State.setV, State.write, State.read])
    | simp only [Option.map_some, State.setV, State.write, State.read]

theorem exec_v {y : Instr} (h : scalarOnly y = true) {s s' : State} (e : exec y s = some s') :
    s'.v = s.v := by
  cases y <;> simp only [scalarOnly, reduceCtorEq] at h <;>
    simp only [reduceExec, State.load, State.store] at e <;> (try split_ifs at e) <;>
    (try simp only [Option.some.injEq, Option.map_some] at e) <;> (try cases e) <;> (try subst e) <;> rfl

private theorem exec_vop (op : VOp) (s : State) :
    exec (.vop op) s = (op.eval s).map fun p => s.setV p.1 p.2 := rfl

theorem comm {x y : Instr} (hx : vecOnly x = true) (hy : scalarOnly y = true) :
    VG.Interleave.CommuteOn isa (fun _ => True) x y := by
  intro s _
  cases x <;> simp only [vecOnly, reduceCtorEq] at hx
  rename_i op
  show (exec (.vop op) s).bind (exec y) = (exec y s).bind (exec (.vop op))
  rw [exec_vop]
  cases hy' : exec y s with
  | none =>
    cases he : op.eval s with
    | none => rfl
    | some p => simp only [Option.map_some, Option.bind_some, exec_setV hy, hy', Option.map_none,
        Option.bind_none]
  | some s' =>
    simp only [Option.bind_some, exec_vop, VOp.eval_congr hx (exec_v hy hy')]
    cases he : op.eval s with
    | none => rfl
    | some p => simp only [Option.map_some, Option.bind_some, exec_setV hy, hy']

/-- A block of vector-only instructions and one of scalar-only ones are independent. -/
theorem indeps {a b : List Instr} (ha : a.all vecOnly = true) (hb : b.all scalarOnly = true) :
    VG.Interleave.Indeps isa (fun _ => True) a b :=
  ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial, fun x hx y hy =>
    comm (List.all_eq_true.mp ha x hx) (List.all_eq_true.mp hb y hy)⟩

end VG.Proof.Sha3.AArch64.Hybrid
