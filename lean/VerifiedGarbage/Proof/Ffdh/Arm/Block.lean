module

public import VerifiedGarbage.Proof.Framework.Block -- shake: keep (ffrun expands WP.of_runBlock and runBlock lemmas in importers)
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd -- shake: keep (ffrun expands these state-update lemmas in importers)
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Impl.Ffdh.Arm.Init
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.Semantics

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

theorem ldrb_exec (s : State) (t n : Reg) (d : Nat) :
    exec (.ldrb t n d) s =
      if d < 4096 then
        if InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 d)) 1 then
          some (s.setReg t ((s.mem (State.addr (s.gpr n + BitVec.ofNat 32 d))).setWidth 32))
        else none
      else none := by
  simp only [exec]
  split
  · simp only [State.load8]
    split <;> rfl
  · rfl

theorem strb_exec (s : State) (t n : Reg) (d : Nat) :
    exec (.strb t n d) s =
      if d < 4096 then
        if InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 d)) 1 then
          some (putMem s (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 d)) ((s.gpr t).setWidth 8)))
        else none
      else none := rfl

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
      | .orr => s.gpr n ||| v | .eor => s.gpr n ^^^ v | .bic => s.gpr n &&& ~~~v)) := rfl

theorem cmp_exec (s : State) (n : Reg) (o : Op2) :
    exec (.cmp n o) s = (o.eval s).map (fun v => subFlags s (s.gpr n) v) := rfl

theorem subs_exec (s : State) (d n : Reg) (o : Op2) :
    exec (.subs d n o) s = (o.eval s).map (fun v =>
      (subFlags s (s.gpr n) v).setReg d (s.gpr n - v)) := rfl

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

/-- `withRest`, its side condition a closed check that every register the
code writes is one of `rs`, proven by `rfl`: `simp` on `clobbers` would
generate the equations of `dstOf`'s match. -/
theorem withRest_all {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa c s Q) (hc : (instrs c).all (fun i => (dsts i).all fun r => decide (r ∈ rs)) = true)
    (noCalls : c.noCalls = true) :
    WP isa c s fun t => Q t ∧ VG.Proof.X25519.Arm.Rest rs s t :=
  withRest rs h (fun _ hr i hi =>
    clobbers_eq_false_of_all (List.all_eq_true.mp hc i hi) (decide_eq_false hr)) noCalls

theorem withAllRest{c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ VG.Proof.X25519.Arm.Rest VG.Proof.Bignum.Arm.roundClobbers s t := by
  obtain ⟨trace, t, run, done⟩ := h
  have perms := VG.Arm.Exec.rdwr run
  exact ⟨trace, t, run, done,
    (by intro r hr; exact False.elim (hr (by cases r <;> decide))), perms.1, perms.2.1, perms.2.2⟩

theorem encodable_byte {v : BitVec 32} (h : v.toNat < 256) : encodable v = true := by
  unfold encodable
  apply List.any_eq_true.mpr
  refine ⟨0, by decide, ?_⟩
  simpa [BitVec.toNat_rotateLeft, Nat.mod_eq_of_lt v.isLt,
    Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt v.isLt] using h

tactic_template "ffrun" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp (disch := decide) only [runBlock_cons, runStep_some, runBlock_nil,
    mov_exec, movw_exec, mul_exec, add_exec, cmp_exec, subs_exec, adc_exec, logic_exec, str_exec, ldr_exec, ldrb_exec, strb_exec, ldrSp_exec, addSp_exec, Op2.eval,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    gpr_subFlags, mem_subFlags, c_subFlags, z_subFlags, RegUpd.c_setReg,
    gpr_putMem, mem_putMem, wr_putMem, rd_putMem, sp_putMem, z_putMem,
    RegUpd.sp_setReg, RegUpd.z_setReg, gpr_mem, mem_mem, wr_mem, rd_mem, sp_mem, z_mem,
    Option.map_some, Option.some.injEq, exists_eq_left',
    ite_true, ite_false, reduceCtorEq, true_and, and_true, encodable_byte,
    Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul,
    BitVec.reduceSub, BitVec.reduceBEq, BitVec.reduceHShiftLeft, BitVec.reduceEq, decide_true, decide_false, $ls,*]))

end VG.Proof.Ffdh.Arm
