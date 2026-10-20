module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseMath
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseState
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Public policy setup in small instruction blocks, without increasing
symbolic-execution budgets for the complete frame initialization. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Bignum.Arm (Workspace)

private theorem flagsWr (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
private theorem flagsSp (s : State) (x y : BitVec 32) : (subFlags s x y).sp = s.sp := rfl

theorem phaseBitHead_ok (q : Bool) (s : State) {bits : Nat} (positive : 0 < bits)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 24#32)) 4)
    (write : InRegions s.wr (State.addr (s.sp + 44#32)) 4)
    (value : s.mem.readW (State.addr (s.sp + 24#32)) 32 = BitVec.ofNat 32 bits) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseBitHead q)) s fun t =>
      (t.gpr .r3 = BitVec.ofNat 32 (phaseBits q bits) ∧
        t.mem = s.mem.writeW (State.addr (s.sp + 44#32)) (BitVec.ofNat 32 (phaseBits q bits))) ∧
        Rest [.r3, .r12] s t := by
  refine withRest [.r3, .r12] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseBitHead q) : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases q <;> cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  have sub : BitVec.ofNat 32 bits - 1 = BitVec.ofNat 32 (bits - 1) := by
    change BitVec.ofNat 32 bits - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive]
  cases q <;> unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phaseBitHead VG.Impl.Ffdh.Arm.ParameterCandidate.save <;>
    ffrun [List.cons_append, List.nil_append, BitVec.add_zero, read, write, value, sub, phaseBits]

theorem phaseWidth_ok (s : State) {bits : Nat} (bound : bits ≤ 8192)
    (value : s.gpr .r3 = BitVec.ofNat 32 bits)
    (write : InRegions s.wr (State.addr (s.sp + 48#32)) 4) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.phaseWidth) s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 48#32)) (BitVec.ofNat 32 ((bits + 7) / 8))) ∧
        Rest [.r4, .r12] s t := by
  refine withRest [.r4, .r12] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.phaseWidth : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phaseWidth VG.Impl.Ffdh.Arm.ParameterCandidate.save
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, value, write, witnessWidth_word bound]

theorem phaseChecks_ok (s : State) {bits : Nat} (positive : 0 < bits) (bound : bits ≤ 8192)
    (value : s.gpr .r3 = BitVec.ofNat 32 bits)
    (write : InRegions s.wr (State.addr (s.sp + 52#32)) 4) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.phaseChecks) s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 52#32)) (BitVec.ofNat 32 (VG.Spec.Ffdh.primeChecks bits))) ∧
        Rest [.r3, .r5, .r12] s t := by
  refine withRest [.r3, .r5, .r12] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.phaseChecks : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  have count := checks_word positive bound
  simp only [show (0 : BitVec 32) = 0#32 from rfl, decide_eq_true_eq] at count
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phaseChecks VG.Impl.Ffdh.Arm.ParameterCandidate.save
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, BitVec.zero_add,
    show (0 : BitVec 32) = 0#32 from rfl, show (2048 : BitVec 32).toNat = 2048 from rfl,
    show encodable (2048 : BitVec 32) = true from by decide,
    value, write, count, decide_eq_true_eq, flagsWr, flagsSp]

theorem phasePassed_ok (s : State) (write : InRegions s.wr (State.addr (s.sp + 56#32)) 4) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.phasePassed) s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 56#32)) (0#32)) ∧ Rest [.r1, .r12] s t := by
  refine withRest [.r1, .r12] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.phasePassed : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phasePassed VG.Impl.Ffdh.Arm.ParameterCandidate.save
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, write,
    show (0 : BitVec 32) = 0#32 from rfl]

end VG.Proof.Ffdh.Arm.ParameterCandidate
