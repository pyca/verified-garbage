module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.TCB.X86_64.State

/-!
# Storing and reloading registers, one instruction at a time

`store_run` and `load_run` take the first instruction of a block, a store
of a register or a load into one, so a save or restore of several
registers is a chain of rewrites.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd

theorem store_run {s : State} {m : MemOp} {r : Reg} (h : InRegions s.wr (s.ea m) 8) (rest : List Instr) :
    runBlock isa (.store m r :: rest) s =
      runBlock isa rest { s with mem := s.mem.writeW (s.ea m) (s.gpr r) } := by
  rw [runBlock_cons]
  simp only [exec, State.store64, h, ite_true, runStep_some]

theorem load_run {s : State} {m : MemOp} {r : Reg} {v : BitVec 64} (h : InRegions (s.rd ++ s.wr) (s.ea m) 8)
    (hv : s.mem.readW (s.ea m) 64 = v) (rest : List Instr) :
    runBlock isa (.mov r (.mem m) :: rest) s = runBlock isa rest (s.setReg r v) := by
  rw [runBlock_cons]
  simp only [exec, readSrc, State.load64, h, ite_true, Option.map_some, runStep_some, hv]

theorem store3_run {s : State} {m₁ m₂ m₃ : MemOp} {r₁ r₂ r₃ : Reg} (h₁ : InRegions s.wr (s.ea m₁) 8)
    (h₂ : InRegions s.wr (s.ea m₂) 8) (h₃ : InRegions s.wr (s.ea m₃) 8) :
    runBlock isa [.store m₁ r₁, .store m₂ r₂, .store m₃ r₃] s = some { s with
      mem := ((s.mem.writeW (s.ea m₁) (s.gpr r₁)).writeW (s.ea m₂) (s.gpr r₂)).writeW (s.ea m₃) (s.gpr r₃) } := by
  rw [store_run h₁, store_run (by exact h₂), store_run (by exact h₃), runBlock_nil]
  rfl

theorem load3_run {s : State} {m₁ m₂ m₃ : MemOp} {r₁ r₂ r₃ : Reg} {v₁ v₂ v₃ : BitVec 64}
    (h₁ : InRegions (s.rd ++ s.wr) (s.ea m₁) 8) (h₂ : InRegions (s.rd ++ s.wr) (s.ea m₂) 8)
    (h₃ : InRegions (s.rd ++ s.wr) (s.ea m₃) 8) (hv₁ : s.mem.readW (s.ea m₁) 64 = v₁)
    (hv₂ : s.mem.readW (s.ea m₂) 64 = v₂) (hv₃ : s.mem.readW (s.ea m₃) 64 = v₃)
    (he₂ : (s.setReg r₁ v₁).ea m₂ = s.ea m₂) (he₃ : ((s.setReg r₁ v₁).setReg r₂ v₂).ea m₃ = s.ea m₃)
    (rest : List Instr) :
    runBlock isa (.mov r₁ (.mem m₁) :: .mov r₂ (.mem m₂) :: .mov r₃ (.mem m₃) :: rest) s =
      runBlock isa rest (((s.setReg r₁ v₁).setReg r₂ v₂).setReg r₃ v₃) := by
  rw [load_run h₁ hv₁, load_run (v := v₂) (by rw [he₂]; exact h₂) (by rw [he₂]; exact hv₂),
    load_run (v := v₃) (by rw [he₃]; exact h₃) (by rw [he₃]; exact hv₃)]

end VG.Proof.TripleDes.X86_64
