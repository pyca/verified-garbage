module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Fixed native local stores used by parameter generation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem saveR1_ok {s : State} {d : Nat} (stack : Workspace s s.sp 72) (fit : d + 4 ≤ 72) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 d)) s fun t =>
      t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 d)) (s.gpr .r1) ∧ Rest [.r12] s t := by
  have write : InRegions s.wr (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.write fit
  have offset : d < 4096 := by omega
  refine withRest [.r12] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 d) : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.save
  ffrun [BitVec.add_zero, write, offset]

theorem saveWord_ok {s : State} {d : Nat} (stack : Workspace s s.sp 72) (fit : d + 4 ≤ 72)
    (value : BitVec 32) (enc : encodable value = true) :
    WP isa (.block (([.mov .r1 (.imm value)] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 d)) s fun t =>
      t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 d)) value ∧ Rest [.r1, .r12] s t := by
  have write : InRegions s.wr (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.write fit
  have offset : d < 4096 := by omega
  refine withRest [.r1, .r12] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block ([.mov .r1 (.imm value)] ++
        VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 d) : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.save
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, write, enc, offset]

end VG.Proof.Ffdh.Arm.ParameterCandidate
