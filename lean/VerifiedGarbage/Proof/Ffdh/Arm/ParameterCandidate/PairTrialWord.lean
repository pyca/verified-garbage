module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialLoopWord
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialDigit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStepWord

/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Bignum.Arm.TrialDivision16
open VG.Impl.Ffdh.Arm.ParameterCandidate

private theorem trialPairRedcWord_ok (s : State) :
    WP isa (.block trialPairRedc) s fun t =>
      (t.gpr .r8 = redcWord (s.gpr .r7) (s.gpr .r8) (s.gpr .r4) (s.gpr .r3) ∧ t.mem = s.mem) ∧
      Rest [.r8, .r7, .r6] s t := by
  unfold trialPairRedc VG.Impl.Bignum.Arm.TrialDivision16.redcAt
  refine wp_dp (op2_reg _ _) fun u1 v1 => wp_mul fun u2 v2 => wp_mov (op2_lsl (by decide)) fun u3 v3 =>
    wp_mov (op2_lsr (by decide)) fun u4 v4 => wp_mul fun u5 v5 => wp_dp (op2_reg _ _) fun u6 v6 =>
      wp_mov (op2_lsr (by decide)) fun t v7 => WP.block_nil ?_
  refine ⟨⟨?_, by rw [v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]⟩,
    (v1.rest (by simp)).trans ((v2.rest (by simp)).trans ((v3.rest (by simp)).trans
      ((v4.rest (by simp)).trans ((v5.rest (by simp)).trans ((v6.rest (by simp)).trans (v7.rest (by simp)))))))⟩
  rw [v7.gpr, v6.gpr, dpVal, v5.gpr, v4.gpr, v3.gpr, v2.gpr, v1.gpr, dpVal,
    v5.other .r7 (by decide), v4.other .r7 (by decide),
    v3.other .r7 (by decide), v2.other .r7 (by decide), v1.gpr, dpVal,
    v4.other .r3 (by decide), v3.other .r3 (by decide), v2.other .r3 (by decide), v1.other .r3 (by decide),
    v1.other .r4 (by decide)]
  rfl


theorem trialPairStepWord_ok (s : State) {n : Nat} (positive : 0<n) (fits : n<2^32)
    (count : s.gpr .r1=BitVec.ofNat 32 n)
    (readLow : InRegions (s.rd++s.wr) (State.addr (s.gpr .r0-1)) 1)
    (readHigh : 1<n → InRegions (s.rd++s.wr) (State.addr (s.gpr .r0-2)) 1) :
    WP isa trialPairStep s fun t =>
      t.gpr .r2=redcWord (trialDigitWord s.mem (s.gpr .r0) n) (s.gpr .r2) (s.gpr .r4) (s.gpr .r3) ∧
      t.gpr .r8=redcWord (trialDigitWord s.mem (s.gpr .r0) n) (s.gpr .r8) (s.gpr .r4) (s.gpr .r3) ∧
      t.gpr .r0=s.gpr .r0-BitVec.ofNat 32 (min 2 n) ∧
      t.gpr .r1=BitVec.ofNat 32 (n-min 2 n) ∧ t.z=decide (n≤2) ∧ t.mem=s.mem ∧
      Rest [.r0,.r1,.r2,.r5,.r6,.r7,.r8] s t := by
  unfold trialPairStep
  refine WP.seq (WP.mono (trialDigit_ok s positive fits count readLow readHigh) ?_)
  rintro u ⟨⟨ptr,cnt,word,mem⟩,rest⟩
  simp only [List.cons_append,List.nil_append]
  refine wp_mov (op2_reg _ _) fun v save => ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (redcWord_ok v) ?_
  rintro x ⟨⟨a,memX⟩,keepX⟩
  rw [WP.block_append_iff]
  refine WP.mono (trialPairRedcWord_ok x) ?_
  rintro y ⟨⟨b,memY⟩,keepY⟩
  refine wp_cmp (op2_imm (by decide)) fun t flags zero => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [flags.gpr,keepY.gpr .r2 (by simp),a,save.other .r5 (by decide),word,
      save.other .r2 (by decide),rest.gpr .r2 (by simp),
      save.other .r4 (by decide),rest.gpr .r4 (by simp),save.other .r3 (by decide),rest.gpr .r3 (by simp)]
    rfl
  · rw [flags.gpr,b,keepX.gpr .r7 (by simp),save.gpr,word,
      keepX.gpr .r8 (by simp),save.other .r8 (by decide),rest.gpr .r8 (by simp),
      keepX.gpr .r4 (by simp),save.other .r4 (by decide),rest.gpr .r4 (by simp),
      keepX.gpr .r3 (by simp),save.other .r3 (by decide),rest.gpr .r3 (by simp)]
    rfl
  · rw [flags.gpr,keepY.gpr .r0 (by simp),keepX.gpr .r0 (by simp),save.other .r0 (by decide),ptr]
  · rw [flags.gpr,keepY.gpr .r1 (by simp),keepX.gpr .r1 (by simp),save.other .r1 (by decide),cnt]
  · rw [zero,keepY.gpr .r1 (by simp),keepX.gpr .r1 (by simp),save.other .r1 (by decide),cnt]
    change (BitVec.ofNat 32 (n-min 2 n)-0#32==0#32)=_
    rw [BitVec.sub_zero]
    change (BitVec.ofNat 32 (n-min 2 n)==(0 : BitVec 32))=_
    rw [ofNat_beq_zero (by omega : n-min 2 n<2^32)]
    exact decide_eq_decide.mpr (by omega)
  · rw [flags.mem,memY,memX,save.mem,mem]
  · exact (rest.mono (by simp)).trans ((save.rest (by simp)).trans ((keepX.mono (by simp)).trans
      ((keepY.mono (by simp)).trans (flags.rest _))))


end VG.Proof.Ffdh.Arm.ParameterCandidate
