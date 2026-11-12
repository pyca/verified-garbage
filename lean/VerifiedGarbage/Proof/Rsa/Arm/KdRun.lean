module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Proof.RsaPss.Arm.Step
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Rsa.Arm.KeyDiv

/-!
# Running the blocks of the key checks' division on ARMv7

`krun`: a block run symbolically (`WP.of_runBlock`, then each instruction's
semantics), as `RsaPss.Arm`'s `prun`, with the flags of `adds` read through.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm

theorem addFlags_gpr (s : State) (x y : BitVec 32) : (addFlags s x y).gpr = s.gpr := rfl
theorem addFlags_mem (s : State) (x y : BitVec 32) : (addFlags s x y).mem = s.mem := rfl
theorem addFlags_rd (s : State) (x y : BitVec 32) : (addFlags s x y).rd = s.rd := rfl
theorem addFlags_wr (s : State) (x y : BitVec 32) : (addFlags s x y).wr = s.wr := rfl
theorem addFlags_sp (s : State) (x y : BitVec 32) : (addFlags s x y).sp = s.sp := rfl
theorem addFlags_z (s : State) (x y : BitVec 32) : (addFlags s x y).z = (x + y == 0) := rfl
theorem c_addFlags (s : State) (x y : BitVec 32) :
    (addFlags s x y).c = decide (2 ^ 32 ≤ x.toNat + y.toNat) := rfl

open VG.Impl.Rsa.Arm.KeyDiv in
theorem slots_lt : sP < 4096 ∧ sD < 4096 ∧ sV < 4096 ∧ sD1 < 4096 ∧ sMk < 4096 ∧ sQ < 4096 ∧ sU0 < 4096 ∧
    sU2 < 4096 ∧ sJ < 4096 ∧ 16 < 4096 ∧ VG.Impl.Rsa.Arm.Keys.sC < 4096 := by decide

/-- `adc`'s carry as a `cond`, whose condition `simp` may rewrite. -/
theorem exec_adc (s : State) (d n : Reg) (op2 : Op2) :
    exec (.adc d n op2) s = (op2.eval s).map fun y => s.setReg d (s.gpr n + y + bif s.c then 1 else 0) := by
  simp only [exec, Bool.cond_eq_ite]

/-- Runs a block symbolically, with `facts`. -/
syntax "krun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| krun) => `(tactic| krun [])
  | `(tactic| krun [$ls,*]) => `(tactic| plain_simp_names (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (disch := decide) only [VG.Arm.runBlock_cons, VG.Arm.runStep_some, VG.Arm.runBlock_nil, ↓exec_adc, exec,
        VG.Proof.RsaPkcs1Sig.Arm.encodable_of_lt, Op2.eval, VG.Arm.RegUpd.gpr_setReg,
        VG.Arm.RegUpd.mem_setReg, VG.Arm.RegUpd.rd_setReg, VG.Arm.RegUpd.wr_setReg,
        VG.Arm.RegUpd.sp_setReg, VG.Arm.RegUpd.z_setReg, VG.Arm.RegUpd.c_setReg,
        VG.Proof.RsaPss.Arm.subFlags_gpr, VG.Proof.RsaPss.Arm.subFlags_mem,
        VG.Proof.RsaPss.Arm.subFlags_rd, VG.Proof.RsaPss.Arm.subFlags_wr, VG.Proof.RsaPss.Arm.subFlags_sp,
        VG.Proof.RsaPss.Arm.subFlags_z, VG.Proof.RsaPss.Arm.c_subFlags,
        addFlags_gpr, addFlags_mem, addFlags_rd, addFlags_wr, addFlags_sp, addFlags_z, c_addFlags,
        State.load32, VG.Proof.RsaPss.Arm.store32_eq,
        VG.Proof.RsaPss.Arm.setMem_gpr, VG.Proof.RsaPss.Arm.setMem_sp, VG.Proof.RsaPss.Arm.setMem_rd,
        VG.Proof.RsaPss.Arm.setMem_wr, VG.Proof.RsaPss.Arm.setMem_mem, VG.Proof.RsaPss.Arm.setMem_z,
        ite_true, ite_false, ↓reduceIte, reduceCtorEq, Nat.reduceLT,
        Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, Option.map_some, Option.some.injEq, exists_eq_left',
        List.cons_append, List.nil_append, and_true, true_and, BitVec.add_zero, slots_lt, $ls,*]))

/-- Two blocks in sequence are their instructions in one block. -/
theorem wp_seq_blocks {a b : List Instr} {c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq (.block a) (.seq (.block b) c)) s Q ↔ WP isa (.seq (.block (a ++ b)) c) s Q := by
  rw [WP.seq_iff, WP.seq_iff, WP.block_append_iff]
  have e : (fun s' => WP isa (.seq (.block b) c) s' Q) = fun s' => WP isa (.block b) s' fun s'' => WP isa c s'' Q :=
    funext fun _ => propext WP.seq_iff
  rw [e]

end VG.Proof.Rsa.Arm.KeyDiv
