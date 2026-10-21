module

import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Mont.X86.Square.DigitStore

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem mul_by_b_eq (s : State) (a : BitVec 32) :
    execMul .ebx (s.setReg .eax a) = execMul .edx ((s.setReg .eax a).setReg .edx (s.gpr .ebx)) := by
  cases s
  simp only [execMul, State.setReg, State.setFlags, show Reg.eax ≠ Reg.edx by decide,
    show Reg.ebx ≠ Reg.eax by decide, ↓reduceIte]
  congr 1
  funext r
  split_ifs <;> simp_all

def prodByB : List Instr := [.mov .eax (.mem (at_ .ebp 0)), .mul .ebx] ++ VG.Impl.Mont.X86.Rt.Square.accum

theorem prodByB_ok {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L)
    (hx : PtrAt s W .ebp x) (xl : x+4≤L) :
    WP isa (.block prodByB) s fun t => t = prodState s (s.mem.readW (off W x) 32) (s.gpr .ebx) := by
  apply WP.of_runBlock
  refine ⟨_, ?_, rfl⟩
  have read := readSrc_ptr hw hx (d := 0) (by omega)
  simp only [Nat.add_zero] at read
  simp only [prodByB, List.cons_append, List.nil_append, runBlock_cons, exec, read,
    Option.map_some, runStep_some, run_accum, mul_by_b_eq, prodState]

end VG.Proof.Mont.X86.Square
