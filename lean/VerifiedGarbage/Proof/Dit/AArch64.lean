module

public import VerifiedGarbage.Impl.Dit.AArch64
meta import VerifiedGarbage.Impl.Dit.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Dit
meta import VerifiedGarbage.Spec.Dit
public import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# Entering and leaving data independent timing on AArch64: the proofs

`enter_verified` and `clear_verified` prove the functions against their
contracts (`Spec/Dit.lean`), which say what every contract can: no memory
written, the calling convention's preserved state kept, constant time.

`enter_dit` and `clear_dit` prove what the contracts cannot name, the
functions' effect on PSTATE.DIT, of every run of their code in the model:
after `vg_dit_enter`, PSTATE.DIT is 1, and `x0` is 1 if it was 1 on entry
and 0 if it was 0; after `vg_dit_clear`, it is 0.
-/

@[expose] public section

namespace VG.Proof.Dit.AArch64
open VG VG.AArch64 VG.Impl.Dit.AArch64 RegUpd

/-- From any state, `vg_dit_enter` runs and ends with PSTATE.DIT on, `x0`
its old value (1 or 0), and the memory and regions unchanged. -/
theorem enter_wp (s : State) :
    WP isa enter s fun t => t.dit = true ∧ t.gpr .x0 = (if s.dit then 1 else 0) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  cases hd : s.dit <;>
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, hd, gpr_write_self,
      mem_write, rd_write, wr_write, BitVec.setWidth_eq, Size.bits, Option.some.injEq,
      exists_eq_left', ite_true, ite_false, Nat.reduceLT, Bool.false_eq_true] <;> decide

/-- Every run of `vg_dit_enter` ends with PSTATE.DIT on, and with `x0` 1 if
PSTATE.DIT was on on entry and 0 if it was off. -/
theorem enter_dit {s s' : State} {t : List Leak} (h : Exec isa enter s t s') :
    s'.dit = true ∧ s'.gpr .x0 = if s.dit then 1 else 0 := by
  obtain ⟨_, _, he, hq⟩ := enter_wp s
  rw [(Exec.det h he).2]
  exact ⟨hq.1, hq.2.1⟩

/-- From any state, `vg_dit_clear` runs and ends with PSTATE.DIT off, and
the registers, memory and regions unchanged. -/
theorem clear_wp (s : State) :
    WP isa clear s fun t => t.dit = false ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left', and_self]

/-- Every run of `vg_dit_clear` ends with PSTATE.DIT off. -/
theorem clear_dit {s s' : State} {t : List Leak} (h : Exec isa clear s t s') :
    s'.dit = false := by
  obtain ⟨_, _, he, hq⟩ := clear_wp s
  rw [(Exec.det h he).2]
  exact hq.1

/-- The contract both functions are proven against, and implies theirs: no
buffer, and only the stack pointer public. -/
def contract : Contract isa where
  pre s := s.rd = [] ∧ s.wr = []
  post _ _ := True
  pub s t := s.sp = t.sp

/-- A state satisfying `contract.pre`. -/
def sat : State where
  gpr _ := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := []

theorem enter_verified : Verified target enter (Spec.Dit.enterContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s _
    obtain ⟨tr, t, he, -⟩ := enter_wp s
    refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, trivial⟩
    intro r hr
    have hc := instrs_keeps (c := enter) (rs := preserved) (by decide +kernel)
    apply Exec.gpr (fun i hi => ?_) he
    simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs []) ?_ (by taint_decide)
    intro s t _ _ h
    exact ⟨h, fun r hr => by simp at hr⟩
  · exact {
      pre := by sig_implies_pre [Spec.Dit.enterContract, Spec.Dit.enterSig, contract, abi, argRegs]
      -- Both postconditions are `True`.
      post := fun _ _ _ _ => trivial
      pub := by sig_implies_pub [Spec.Dit.enterContract, Spec.Dit.enterSig, contract, abi, argRegs]
      sat := by sig_implies_sat [Spec.Dit.enterContract, Spec.Dit.enterSig, contract, abi, argRegs] [sat] using sat }

theorem clear_verified : Verified target clear (Spec.Dit.clearContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s _
    obtain ⟨tr, t, he, -⟩ := clear_wp s
    refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, trivial⟩
    intro r hr
    have hc := instrs_keeps (c := clear) (rs := preserved) (by decide +kernel)
    apply Exec.gpr (fun i hi => ?_) he
    simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs []) ?_ (by taint_decide)
    intro s t _ _ h
    exact ⟨h, fun r hr => by simp at hr⟩
  · exact {
      pre := by sig_implies_pre [Spec.Dit.clearContract, Spec.Dit.clearSig, contract, abi, argRegs]
      -- Both postconditions are `True`.
      post := fun _ _ _ _ => trivial
      pub := by sig_implies_pub [Spec.Dit.clearContract, Spec.Dit.clearSig, contract, abi, argRegs]
      sat := by sig_implies_sat [Spec.Dit.clearContract, Spec.Dit.clearSig, contract, abi, argRegs] [sat] using sat }

end VG.Proof.Dit.AArch64
