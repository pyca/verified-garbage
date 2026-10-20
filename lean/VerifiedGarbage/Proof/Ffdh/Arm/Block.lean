module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Impl.Ffdh.Arm.Init
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Framework.Arm.Inline

/-! Symbolic execution of the short ARMv7 FFDH argument and controller blocks. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.RegUpd

theorem gpr_mem (s : State) (m : Mem) (r : Reg) :
    ({s with mem := m} : State).gpr r = s.gpr r := rfl
theorem wr_mem (s : State) (m : Mem) : ({s with mem := m} : State).wr = s.wr := rfl
theorem rd_mem (s : State) (m : Mem) : ({s with mem := m} : State).rd = s.rd := rfl
theorem mem_mem (s : State) (m : Mem) : ({s with mem := m} : State).mem = m := rfl
theorem sp_mem (s : State) (m : Mem) : ({s with mem := m} : State).sp = s.sp := rfl
theorem z_mem (s : State) (m : Mem) : ({s with mem := m} : State).z = s.z := rfl

theorem mov_exec (s : State) (d : Reg) (o : Op2) :
    exec (.mov d o) s = (o.eval s).map (s.setReg d) := rfl
theorem movw_exec (s : State) (d : Reg) (v : BitVec 16) :
    exec (.movw d v) s = some (s.setReg d (v.setWidth 32)) := rfl
theorem mul_exec (s : State) (d a b : Reg) :
    exec (.mul d a b) s = some (s.setReg d (s.gpr a * s.gpr b)) := rfl
theorem add_exec (s : State) (d a : Reg) (o : Op2) :
    exec (.dp .add d a o) s = (o.eval s).map (fun b => s.setReg d (s.gpr a + b)) := rfl

def putMem (s : State) (m : Mem) : State := {s with mem := m}

theorem gpr_putMem (s : State) (m : Mem) (r : Reg) : (putMem s m).gpr r = s.gpr r := rfl
theorem mem_putMem (s : State) (m : Mem) : (putMem s m).mem = m := rfl
theorem wr_putMem (s : State) (m : Mem) : (putMem s m).wr = s.wr := rfl
theorem rd_putMem (s : State) (m : Mem) : (putMem s m).rd = s.rd := rfl
theorem sp_putMem (s : State) (m : Mem) : (putMem s m).sp = s.sp := rfl
theorem z_putMem (s : State) (m : Mem) : (putMem s m).z = s.z := rfl

theorem str_exec (s : State) (t n : Reg) (d : Nat) :
    exec (.str t n d) s =
      if d < 4096 then
        if InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 d)) 4 then
          some (putMem s (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 d)) (s.gpr t)))
        else none
      else none := rfl

theorem ldr_exec (s : State) (t n : Reg) (d : Nat) :
    exec (.ldr t n d) s =
      if d < 4096 then
        if InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 d)) 4 then
          some (s.setReg t (s.mem.readW (State.addr (s.gpr n + BitVec.ofNat 32 d)) 32))
        else none
      else none := by
  simp only [exec]
  split
  · simp only [State.load32]
    split <;> rfl
  · rfl

theorem ldrSp_exec (s : State) (r : Reg) (d : Nat) :
    exec (.ldrSp r d) s =
      if d < 4096 then
        if InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 d)) 4 then
          some (s.setReg r (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 d)) 32))
        else none
      else none := by
  simp only [exec]
  split
  · simp only [State.load32]
    split <;> rfl
  · rfl

theorem addSp_exec (s : State) (r : Reg) (d : Nat) :
    exec (.addSp r d) s = if d < 256 then some (s.setReg r (s.sp + BitVec.ofNat 32 d)) else none := rfl

theorem logic_exec (s : State) (op : DpOp) (d n : Reg) (o : Op2) :
    exec (.dp op d n o) s = (o.eval s).map (fun v => s.setReg d
      (match op with
      | .add => s.gpr n + v | .sub => s.gpr n - v | .and => s.gpr n &&& v
      | .orr => s.gpr n ||| v | .eor => s.gpr n ^^^ v)) := rfl

theorem cmp_exec (s : State) (n : Reg) (o : Op2) :
    exec (.cmp n o) s = (o.eval s).map (fun v => subFlags s (s.gpr n) v) := rfl

theorem adc_exec (s : State) (d n : Reg) (o : Op2) :
    exec (.adc d n o) s = (o.eval s).map
      (fun v => s.setReg d (s.gpr n + v + (if s.c then 1 else 0))) := rfl

theorem gpr_subFlags (s : State) (a b : BitVec 32) (r : Reg) :
    (subFlags s a b).gpr r = s.gpr r := rfl
theorem mem_subFlags (s : State) (a b : BitVec 32) : (subFlags s a b).mem = s.mem := rfl
theorem c_subFlags (s : State) (a b : BitVec 32) :
    (subFlags s a b).c = decide (b.toNat ≤ a.toNat) := rfl
theorem z_subFlags (s : State) (a b : BitVec 32) :
    (subFlags s a b).z = (a - b == 0) := rfl

theorem withRest {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa c s Q) (hc : ∀ r, r ∉ rs → ∀ i ∈ instrs c, clobbers i r = false)
    (noCalls : c.noCalls = true) :
    WP isa c s fun t => Q t ∧ VG.Proof.X25519.Arm.Rest rs s t := by
  obtain ⟨trace, t, run, done⟩ := h
  have perms := VG.Arm.Exec.rdwr run
  exact ⟨trace, t, run, done, fun r hr => VG.Arm.Exec.gpr (hc r hr) run (.inl noCalls),
    perms.1, perms.2.1, perms.2.2⟩

tactic_template "ffrun" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp (config := { decide := true }) (disch := decide) only [runBlock_cons, runStep_some, runBlock_nil,
    mov_exec, movw_exec, mul_exec, add_exec, cmp_exec, adc_exec, logic_exec, str_exec, ldr_exec, ldrSp_exec, addSp_exec, Op2.eval,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    gpr_subFlags, mem_subFlags, c_subFlags, z_subFlags, RegUpd.c_setReg,
    gpr_putMem, mem_putMem, wr_putMem, rd_putMem, sp_putMem, z_putMem,
    RegUpd.sp_setReg, RegUpd.z_setReg, gpr_mem, mem_mem, wr_mem, rd_mem, sp_mem, z_mem,
    Option.map_some, Option.some.injEq, exists_eq_left',
    ite_true, ite_false, reduceCtorEq, true_and, and_true, $ls,*]))

end VG.Proof.Ffdh.Arm
