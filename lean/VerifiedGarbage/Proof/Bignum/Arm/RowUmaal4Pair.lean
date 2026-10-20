module

public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal
import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Permissions
import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Step
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal

/-! Successful pair bodies expose their four permissions and exact state. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

def wordTraceU (k : Nat) (s : State) : List Leak :=
  [.addr (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)), .addr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)),
    .addr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k))]

theorem rowBodyU_forward {s t : State} {tr : List Leak}
    (h : Exec isa (.block rowBodyU) s tr t) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + 0#32)) 4 ∧
    InRegions s.wr (State.addr (s.gpr .r0 + 0#32)) 4 ∧
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + 4#32)) 4 ∧
    InRegions s.wr (State.addr (s.gpr .r0 + 4#32)) 4 ∧
    t = advState (stepNew 4 (stepNew 0 s)) ∧ tr = wordTraceU 0 s ++ wordTraceU 4 s := by
  have split : Exec isa (.block (rowFirstAtU 0 ++ (rowStepU 4 ++ rowAdvance2))) s tr t := by
    simpa only [rowBodyU, rowFirstAtU, rowFirstU, List.append_assoc] using h
  obtain ⟨a, t0, ta, e0, tail, rfl⟩ := block_append_inv split
  obtain ⟨b, t4, tb, e4, ea, rfl⟩ := block_append_inv tail
  obtain ⟨r0, w0⟩ := firstAtU_permissions (by decide : 0 < 4096) e0
  have canonical0 := Exec.block_iff.mpr (rowFirstAtU_exec (by decide : 0 < 4096) s r0 w0)
  obtain ⟨rfl, rfl⟩ := Exec.det canonical0 e0
  obtain ⟨r4', w4'⟩ := stepU_permissions (by decide : 4 < 4096) e4
  have r4 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + 4#32)) 4 := by
    simpa only [stepNew, gpr_setReg, rd_setReg, wr_setReg, reduceCtorEq, ↓reduceIte] using r4'
  have w4 : InRegions s.wr (State.addr (s.gpr .r0 + 4#32)) 4 := by
    simpa only [stepNew, gpr_setReg, wr_setReg, reduceCtorEq, ↓reduceIte] using w4'
  have canonical4 := Exec.block_iff.mpr (rowStepU_exec (by decide : 4 < 4096) _ r4' w4')
  obtain ⟨rfl, rfl⟩ := Exec.det canonical4 e4
  have canonicalA := Exec.block_iff.mpr (advState_exec (stepNew 4 ((stepNew 0 s).setReg .r5 (s.gpr .r5))))
  obtain ⟨rfl, rfl⟩ := Exec.det canonicalA ea
  refine ⟨r0, w0, r4, w4, ?_, ?_⟩
  · rw [stepNew_set5]
  · simp only [List.append_nil, wordTraceU, stepNew, gpr_setReg, reduceCtorEq, ↓reduceIte]

end VG.Proof.Bignum.Arm
