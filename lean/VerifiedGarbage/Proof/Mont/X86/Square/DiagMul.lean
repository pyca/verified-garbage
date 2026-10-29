module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.Mont.X86.MulRt
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Mont.X86.Square.DiagPtr
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.X86.Square.Step

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem mul_self_eq (s : State) (a : BitVec 32) :
    execMul .eax (s.setReg .eax a) = execMul .edx ((s.setReg .eax a).setReg .edx a) := by
  cases s
  simp only [execMul, State.setReg, State.setFlags, show Reg.eax ≠ Reg.edx by decide, ↓reduceIte]
  congr 1
  funext r
  split_ifs <;> simp_all

def diagMul : List Instr := [.mov .eax (.mem (at_ .eax 0)), .mul .eax] ++ VG.Impl.Mont.X86.Rt.Square.accum

theorem diagMul_ok {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L)
    (hx : PtrAt s W .eax x) (xl : x+4 ≤ L) :
    WP isa (.block diagMul) s fun t => t = prodState s (s.mem.readW (off W x) 32) (s.mem.readW (off W x) 32) := by
  apply WP.of_runBlock
  refine ⟨_, ?_, rfl⟩
  have read := readSrc_ptr hw hx (d := 0) (by omega)
  simp only [Nat.add_zero] at read
  simp only [diagMul, List.cons_append, List.nil_append, runBlock_cons, exec, read,
    Option.map_some, runStep_some, run_accum, mul_self_eq, prodState]

end VG.Proof.Mont.X86.Square
