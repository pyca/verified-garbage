module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate

theorem trialPairFlag_ok (s : State) :
    WP isa trialPairFlag s fun t =>
      t.z=((s.gpr .r2==0 || s.gpr .r2==s.gpr .r3) || (s.gpr .r8==0 || s.gpr .r8==s.gpr .r3)) ∧
      t.mem=s.mem ∧ Rest [.r2] s t := by
  unfold trialPairFlag
  rw [WP.seq_iff]
  refine WP.mono (trialFlag_ok s) ?_
  rintro u ⟨flag,memory,rest⟩
  cases first : (s.gpr .r2==0 || s.gpr .r2==s.gpr .r3) with
  | true =>
    refine WP.ite true (by change some u.z=some true;rw [flag,first]) ?_ (by intro h;cases h)
    intro _
    refine WP.block_nil ⟨?_,memory,rest.mono (by simp)⟩
    rw [flag,first];rfl
  | false =>
    refine WP.ite false (by change some u.z=some false;rw [flag,first]) (by intro h;cases h) ?_
    intro _
    refine WP.seq (wp_mov (op2_reg _ _) fun v upd => WP.block_nil ?_)
    refine WP.mono (trialFlag_ok v) ?_
    rintro t ⟨last,memT,restT⟩
    refine ⟨?_,memT.trans (upd.mem.trans memory),
      (rest.mono (by simp)).trans ((upd.rest (by simp)).trans (restT.mono (by simp)))⟩
    rw [last,upd.gpr,rest.gpr .r8 (by simp),upd.other .r3 (by decide),rest.gpr .r3 (by simp)]
    rfl


end VG.Proof.Ffdh.Arm.ParameterCandidate
