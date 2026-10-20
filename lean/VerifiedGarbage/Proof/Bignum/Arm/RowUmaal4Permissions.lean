module

import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal4
import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Step
import VerifiedGarbage.Proof.Framework.Semantics

/-! Recover the memory permissions of successful materialized-carry steps. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem block_append_inv {a b : List Instr} {s t : State} {tr : List Leak}
    (h : Exec isa (.block (a ++ b)) s tr t) :
    ∃ u ta tb, Exec isa (.block a) s ta u ∧ Exec isa (.block b) u tb t ∧ tr = ta ++ tb := by
  have e := Exec.block_iff.mp h
  rw [execBlock_append] at e
  cases ea : execBlock isa a s with
  | none => simp only [ea, Option.bind_none, reduceCtorEq] at e
  | some p =>
    rcases p with ⟨u, ta⟩
    cases eb : execBlock isa b u with
    | none => simp only [ea, Option.bind_some, eb, Option.map_none, reduceCtorEq] at e
    | some p =>
      rcases p with ⟨v, tb⟩
      simp only [ea, Option.bind_some, eb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨u, ta, tb, Exec.block_iff.mpr ea, Exec.block_iff.mpr eb, rfl⟩

theorem firstAtU_permissions {k : Nat} (hk : k < 4096) {s t : State} {tr : List Leak}
    (h : Exec isa (.block (rowFirstAtU k)) s tr t) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)) 4 ∧
    InRegions s.wr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 4 := by
  have e := Exec.block_iff.mp h
  by_cases hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)) 4
  · by_cases ha : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 4
    · by_cases hw : InRegions s.wr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 4
      · exact ⟨hr, hw⟩
      · simp [rowFirstAtU, execBlock, isa, exec, hk, State.load32, State.store32,
          hr, ha, hw, gpr_setReg, rd_setReg, wr_setReg] at e
    · simp [rowFirstAtU, execBlock, isa, exec, hk, State.load32,
        hr, ha, gpr_setReg, rd_setReg, wr_setReg] at e
  · simp [rowFirstAtU, execBlock, isa, exec, hk, State.load32, hr] at e

theorem stepU_permissions {k : Nat} (hk : k < 4096) {s t : State} {tr : List Leak}
    (h : Exec isa (.block (rowStepU k)) s tr t) :
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)) 4 ∧
    InRegions s.wr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 4 := by
  have e := Exec.block_iff.mp h
  by_cases hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)) 4
  · by_cases ha : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 4
    · by_cases hw : InRegions s.wr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 4
      · exact ⟨hr, hw⟩
      · simp [rowStepU, execBlock, isa, exec, hk, State.load32, State.store32, Op2.eval,
          hr, ha, hw, gpr_setReg, rd_setReg, wr_setReg, mem_setReg] at e
    · simp [rowStepU, execBlock, isa, exec, hk, State.load32,
        hr, ha, gpr_setReg, rd_setReg, wr_setReg] at e
  · simp [rowStepU, execBlock, isa, exec, hk, State.load32, hr] at e

end VG.Proof.Bignum.Arm
