module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedParams
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The native header limits the first p phase to one round or subtracts that round. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem phaseLimit_ok (first : Bool) {s : State} {checks : Nat} (positive : 0 < checks)
    (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 52#32)) 32 = BitVec.ofNat 32 checks) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseLimit first)) s fun t =>
      t.mem = s.mem.writeW (State.addr (s.sp + 52#32)) (BitVec.ofNat 32 (limitedChecks first checks)) ∧
      Rest [.r1, .r12] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 52#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read (by decide)
  have write : InRegions s.wr (State.addr (s.sp + 52#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.write (by decide)
  have subtract : BitVec.ofNat 32 checks - 1 = BitVec.ofNat 32 (checks - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  refine withRest [.r1, .r12] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseLimit first) : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases first <;> cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phaseLimit VG.Impl.Ffdh.Arm.ParameterCandidate.save limitedChecks
  cases first <;> ffrun [List.cons_append, List.nil_append, BitVec.add_zero, read, write, saved, subtract]
  all_goals rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
