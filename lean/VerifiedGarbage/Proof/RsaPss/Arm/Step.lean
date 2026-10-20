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

theorem exec_movw (s : State) (d : Reg) (imm : BitVec 16) :
    exec (.movw d imm) s = some (s.setReg d (imm.setWidth 32)) := rfl

theorem exec_addSp (s : State) (d : Reg) {imm : Nat} (h : imm < 256) :
    exec (.addSp d imm) s = some (s.setReg d (s.sp + BitVec.ofNat 32 imm)) := by
  simp only [exec, h, ite_true]

theorem exec_dp_reg (s : State) (op : DpOp) (d n m : Reg) :
    exec (.dp op d n (.reg m)) s = some (s.setReg d (VG.Proof.X25519.Arm.dpVal op (s.gpr n) (s.gpr m))) := by
  cases op <;> rfl

theorem exec_dp_imm (s : State) (op : DpOp) (d n : Reg) {v : BitVec 32} (h : encodable v = true) :
    exec (.dp op d n (.imm v)) s = some (s.setReg d (VG.Proof.X25519.Arm.dpVal op (s.gpr n) v)) := by
  cases op <;> simp [exec, Op2.eval, h, VG.Proof.X25519.Arm.dpVal]

theorem exec_dp_lsr (s : State) (op : DpOp) (d n m : Reg) {k : Nat} (h : 1 ≤ k ∧ k ≤ 31) :
    exec (.dp op d n (.shifted m .lsr k)) s =
      some (s.setReg d (VG.Proof.X25519.Arm.dpVal op (s.gpr n) (s.gpr m >>> k))) := by
  cases op <;> simp [exec, Op2.eval, h, VG.Proof.X25519.Arm.dpVal]

theorem exec_dp_lsl (s : State) (op : DpOp) (d n m : Reg) {k : Nat} (h : 1 ≤ k ∧ k ≤ 31) :
    exec (.dp op d n (.shifted m .lsl k)) s =
      some (s.setReg d (VG.Proof.X25519.Arm.dpVal op (s.gpr n) (s.gpr m <<< k))) := by
  cases op <;> simp [exec, Op2.eval, h, VG.Proof.X25519.Arm.dpVal]

theorem exec_dp_one (s : State) (op : DpOp) (d n : Reg) :
    exec (.dp op d n (.imm 1)) s = some (s.setReg d (VG.Proof.X25519.Arm.dpVal op (s.gpr n) 1)) :=
  exec_dp_imm s op d n (v := 1) (by decide)

theorem exec_dp_ff (s : State) (op : DpOp) (d n : Reg) :
    exec (.dp op d n (.imm 0xFF)) s = some (s.setReg d (VG.Proof.X25519.Arm.dpVal op (s.gpr n) 0xFF)) :=
  exec_dp_imm s op d n (v := 0xFF) (by decide)

theorem exec_dp_bc (s : State) (op : DpOp) (d n : Reg) :
    exec (.dp op d n (.imm 0xbc)) s = some (s.setReg d (VG.Proof.X25519.Arm.dpVal op (s.gpr n) 0xbc)) :=
  exec_dp_imm s op d n (v := 0xbc) (by decide)

theorem exec_cmp_zero (s : State) (n : Reg) : exec (.cmp n (.imm 0)) s = some (subFlags s (s.gpr n) 0) := by
  simp [exec, Op2.eval]; rfl

theorem exec_subs_one (s : State) (d n : Reg) :
    exec (.subs d n (.imm 1)) s = some ((subFlags s (s.gpr n) 1).setReg d (s.gpr n - 1)) := by
  simp [exec, Op2.eval]; rfl

theorem exec_mov_reg (s : State) (d m : Reg) : exec (.mov d (.reg m)) s = some (s.setReg d (s.gpr m)) := rfl

theorem exec_mov_imm (s : State) (d : Reg) {v : BitVec 32} (h : encodable v = true) :
    exec (.mov d (.imm v)) s = some (s.setReg d v) := by
  simp [exec, Op2.eval, h]

theorem exec_mov_lsr (s : State) (d m : Reg) {k : Nat} (h : 1 ≤ k ∧ k ≤ 31) :
    exec (.mov d (.shifted m .lsr k)) s = some (s.setReg d (s.gpr m >>> k)) := by
  simp [exec, Op2.eval, h]

theorem exec_mov_lsl (s : State) (d m : Reg) {k : Nat} (h : 1 ≤ k ∧ k ≤ 31) :
    exec (.mov d (.shifted m .lsl k)) s = some (s.setReg d (s.gpr m <<< k)) := by
  simp [exec, Op2.eval, h]

theorem exec_cmp_reg (s : State) (n m : Reg) : exec (.cmp n (.reg m)) s = some (subFlags s (s.gpr n) (s.gpr m)) :=
  rfl

theorem exec_cmp_imm (s : State) (n : Reg) {v : BitVec 32} (h : encodable v = true) :
    exec (.cmp n (.imm v)) s = some (subFlags s (s.gpr n) v) := by
  simp [exec, Op2.eval, h]

theorem exec_ldrSp (s : State) (t : Reg) {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4) :
    exec (.ldrSp t off) s = some (s.setReg t (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) := by
  simp only [exec, ho, ite_true, State.load32, h, Option.map_some]

theorem exec_strR (s : State) (t n : Reg) {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4) :
    exec (.str t n off) s =
      some (setMem s (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) (s.gpr t))) :=
  exec_str ho h

theorem exec_ldrbR (s : State) (t n : Reg) {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 off)) 1) :
    exec (.ldrb t n off) s = some (s.setReg t ((s.mem (State.addr (s.gpr n + BitVec.ofNat 32 off))).setWidth 32)) := by
  simp only [exec, ho, ite_true, State.load8, h, Option.map_some]

theorem exec_strbR (s : State) (t n : Reg) {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 1) :
    exec (.strb t n off) s =
      some (setMem s (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) ((s.gpr t).setWidth 8))) := by
  simp only [exec, ho, ite_true, State.store8, h]; rfl

theorem subFlags_gpr (s : State) (x y : BitVec 32) : (subFlags s x y).gpr = s.gpr := rfl
theorem subFlags_mem (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl
theorem subFlags_rd (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl
theorem subFlags_wr (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
theorem subFlags_sp (s : State) (x y : BitVec 32) : (subFlags s x y).sp = s.sp := rfl
theorem subFlags_z (s : State) (x y : BitVec 32) : (subFlags s x y).z = (x - y == 0) := rfl

theorem gpr_setReg' (s : State) (d : Reg) (x : BitVec 32) (r : Reg) :
    (s.setReg d x).gpr r = if r = d then x else s.gpr r := rfl

theorem setWidth_zero16 : (0#16).setWidth 32 = (0 : BitVec 32) := rfl

theorem encodable_small {v : Nat} (h : v < 256) : encodable (BitVec.ofNat 32 v) = true :=
  VG.Proof.RsaPkcs1Sig.Arm.encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega)

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

