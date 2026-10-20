module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Count successful witnesses, stopping exactly at the phase's policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

private theorem passHead_ok {s : State} {passed checks : Nat} (stack : Workspace s s.sp 72)
    (more : passed < checks) (bound : checks ≤ 128)
    (savedPassed : s.mem.readW (State.addr (s.sp + 56#32)) 32 = BitVec.ofNat 32 passed)
    (savedChecks : s.mem.readW (State.addr (s.sp + 52#32)) 32 = BitVec.ofNat 32 checks) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.onPassHead) s fun t =>
      (t.gpr .r1 = BitVec.ofNat 32 (passed + 1) ∧ t.z = decide (passed + 1 = checks) ∧ t.mem = s.mem) ∧
      Rest [.r1, .r2] s t := by
  have reads (d : Nat) (fit : d + 4 ≤ 72) : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read fit
  have increment : BitVec.ofNat 32 passed + 1 = BitVec.ofNat 32 (passed + 1) := by
    change BitVec.ofNat 32 passed + BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_add_ofNat _ _
  have zero : (BitVec.ofNat 32 (passed + 1) - BitVec.ofNat 32 checks == 0) = decide (passed + 1 = checks) :=
    (sub_beq_zero _ _).trans (ofNat_beq_eq (by omega) (by omega))
  refine withRest [.r1, .r2] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.onPassHead : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.onPassHead
  ffrun [BitVec.add_zero, reads 56 (by decide), reads 52 (by decide), savedPassed, savedChecks, increment, zero]

private theorem passChoice_ok {s : State} {passed checks : Nat} (zero : s.z = decide (passed + 1 = checks)) :
    WP isa (.ite .eq (.block [.mov .r3 (.imm 1)]) (.block [.mov .r3 (.imm 4)])) s fun t =>
      t.gpr .r3 = BitVec.ofNat 32 (if passed + 1 = checks then 1 else 4) ∧ t.mem = s.mem ∧ Rest [.r3] s t := by
  by_cases done : passed + 1 = checks
  · refine WP.ite true (by change some s.z = some true; simp only [zero, done, decide_true]) ?_ (by intro h; cases h)
    intro _
    refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
    refine ⟨?_, u.mem, u.rest (by simp)⟩
    simp only [done, ite_true]
    exact u.gpr
  · refine WP.ite false (by change some s.z = some false; simp only [zero, done, decide_false]) (by intro h; cases h) ?_
    intro _
    refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
    refine ⟨?_, u.mem, u.rest (by simp)⟩
    simp only [done, ite_false]
    exact u.gpr

private theorem passFinish_ok {s : State} (stack : Workspace s s.sp 72) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.onPassFinish) s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 56#32)) (s.gpr .r1) ∧ t.z = (s.gpr .r3 == 4)) ∧ Rest [.r12] s t := by
  have write : InRegions s.wr (State.addr (s.sp + 56#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.write (by decide)
  refine withRest [.r12] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.onPassFinish : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.onPassFinish VG.Impl.Ffdh.Arm.ParameterCandidate.save
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, write]
  exact sub_beq_zero _ _

theorem onPass_ok {s : State} {passed checks : Nat} (stack : Workspace s s.sp 72)
    (more : passed < checks) (bound : checks ≤ 128)
    (savedPassed : s.mem.readW (State.addr (s.sp + 56#32)) 32 = BitVec.ofNat 32 passed)
    (savedChecks : s.mem.readW (State.addr (s.sp + 52#32)) 32 = BitVec.ofNat 32 checks) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.onPass s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 56#32)) (BitVec.ofNat 32 (passed + 1)) ∧
        t.gpr .r3 = BitVec.ofNat 32 (if passed + 1 = checks then 1 else 4) ∧
        t.z = decide (passed + 1 ≠ checks)) ∧ Rest [.r1, .r2, .r3, .r12] s t := by
  simp only [VG.Impl.Ffdh.Arm.ParameterCandidate.onPass, VG.Impl.Ffdh.Arm.ParameterCandidate.seqs]
  refine WP.seq (WP.mono (passHead_ok stack more bound savedPassed savedChecks) ?_)
  rintro u ⟨⟨valueU, zeroU, memU⟩, restU⟩
  refine WP.seq (WP.mono (passChoice_ok zeroU) ?_)
  rintro v ⟨valueV, memV, restV⟩
  have restUV : Rest [.r1, .r2, .r3] s v := (restU.mono (by simp)).trans (restV.mono (by simp))
  have stackV : Workspace v v.sp 72 := by rw [restUV.sp]; exact stack.congr restUV.wr
  refine WP.seq (WP.mono (passFinish_ok stackV) ?_)
  rintro t ⟨⟨memT, zeroT⟩, restT⟩
  refine WP.block_nil ⟨⟨?_, (restT.gpr .r3 (by simp)).trans valueV, ?_⟩,
    (restUV.mono (by simp)).trans (restT.mono (by simp))⟩
  · rw [memT, restV.gpr .r1 (by simp), valueU, memV, memU, restUV.sp]
  · rw [zeroT, valueV]
    by_cases done : passed + 1 = checks <;> simp [done]

end VG.Proof.Ffdh.Arm.ParameterCandidate
