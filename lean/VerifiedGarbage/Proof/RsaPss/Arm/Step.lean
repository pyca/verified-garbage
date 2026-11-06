module

public import VerifiedGarbage.Proof.RsaPss.Arm.Base
public import VerifiedGarbage.Proof.Framework.PlainSimp
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSASSA-PSS on ARMv7: running a block symbolically

Rewrite rules for `exec` of each instruction the blocks use, stated so that
`simp` steps through a block (`WP.of_runBlock`, then `runBlock_cons`,
`runStep_some` and `runBlock_nil`), discharging the permissions of loads and
stores from facts about the state the block starts in (the permissions and
the stack pointer of every later state are its own, by `RegUpd`), and
reading registers through the writes with `RegUpd.gpr_setReg`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm

/-- `s` with memory `m`. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

@[simp] theorem setMem_gpr (s : State) (m : Mem) : (setMem s m).gpr = s.gpr := rfl
@[simp] theorem setMem_sp (s : State) (m : Mem) : (setMem s m).sp = s.sp := rfl
@[simp] theorem setMem_rd (s : State) (m : Mem) : (setMem s m).rd = s.rd := rfl
@[simp] theorem setMem_wr (s : State) (m : Mem) : (setMem s m).wr = s.wr := rfl
@[simp] theorem setMem_mem (s : State) (m : Mem) : (setMem s m).mem = m := rfl
@[simp] theorem setMem_z (s : State) (m : Mem) : (setMem s m).z = s.z := rfl

theorem subFlags_gpr (s : State) (x y : BitVec 32) : (subFlags s x y).gpr = s.gpr := rfl
theorem subFlags_mem (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl
theorem subFlags_rd (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl
theorem subFlags_wr (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
theorem subFlags_sp (s : State) (x y : BitVec 32) : (subFlags s x y).sp = s.sp := rfl
theorem subFlags_z (s : State) (x y : BitVec 32) : (subFlags s x y).z = (x - y == 0) := rfl

theorem setWidth_zero16 : (0#16).setWidth 32 = (0 : BitVec 32) := rfl

theorem movw_val {v : Nat} (h : v < 2 ^ 16) : (BitVec.ofNat 16 v).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

end VG.Proof.RsaPss.Arm

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.RsaPss.Arm

/-! The slots' offsets are immediates. -/

theorem sS_lt : sS < 4096 := by decide
theorem sLo_lt : sLo < 4096 := by decide
theorem sC_lt : sC < 4096 := by decide
theorem sDb_lt : sDb < 4096 := by decide
theorem sL_lt : sL < 4096 := by decide
theorem sNb_lt : sNb < 4096 := by decide
theorem sBi_lt : sBi < 4096 := by decide
theorem sCtr_lt : sCtr < 4096 := by decide
theorem sDone_lt : sDone < 4096 := by decide
theorem sAcc_lt : sAcc < 4096 := by decide
theorem sPos_lt : sPos < 4096 := by decide
theorem sA_lt : sA < 4096 := by decide
theorem sD_lt : sD < 4096 := by decide
theorem sPc_lt : sPc < 4096 := by decide
theorem sAny_lt : sAny < 4096 := by decide

theorem store32_eq (s : State) (a : Addr) (x : BitVec 32) :
    s.store32 a x = if InRegions s.wr a 4 then some (setMem s (s.mem.writeW a x)) else none := rfl
theorem store8_eq (s : State) (a : Addr) (x : BitVec 8) :
    s.store8 a x = if InRegions s.wr a 1 then some (setMem s (s.mem.writeW a x)) else none := rfl
theorem c_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).c = decide (y.toNat ≤ x.toNat) := rfl

/-- Runs a block symbolically: `WP.of_runBlock`, then each instruction's
semantics, reading registers through the writes (`RegUpd`) and keeping
memory and flag updates folded (`setMem`, `subFlags`), with `facts` (the
permissions of the accesses, the values of shift amounts and immediates the
code takes as parameters). -/
syntax "prun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| prun) => `(tactic| prun [])
  | `(tactic| prun [$ls,*]) => `(tactic| plain_simp_names (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (disch := decide) only [runBlock_cons, runStep_some, runBlock_nil, exec,
        VG.Proof.RsaPkcs1Sig.Arm.encodable_of_lt, Op2.eval, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg,
        z_setReg, c_setReg, subFlags_gpr, subFlags_mem, subFlags_rd, subFlags_wr, subFlags_sp, subFlags_z,
        c_subFlags, State.load32, store32_eq, State.load8, store8_eq, setMem_gpr, setMem_sp, setMem_rd,
        setMem_wr, setMem_mem, setMem_z, ite_true, ite_false, ↓reduceIte, reduceCtorEq, Nat.reduceLT,
        Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, Option.map_some, Option.some.injEq, exists_eq_left',
        List.cons_append, List.nil_append, and_true, true_and, BitVec.add_zero, sS_lt, sLo_lt, sC_lt, sDb_lt, sL_lt,
        sNb_lt, setWidth_zero16, sBi_lt, sCtr_lt, sDone_lt, sAcc_lt, sPos_lt, sA_lt, sD_lt, sPc_lt, sAny_lt, $ls,*]))

end VG.Proof.RsaPss.Arm

