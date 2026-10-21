module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairTrialRedc
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialDigit
import VerifiedGarbage.Proof.Bignum.Arm.TrialDivision16
import VerifiedGarbage.Proof.Framework.Omega

/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate

theorem trialPairStep_ok (s : State) {n acc offset divisor inverse : Nat}
    (positive : 0<n) (fits : n<2^32) (count : s.gpr .r1=BitVec.ofNat 32 n)
    (readLow : InRegions (s.rd++s.wr) (State.addr (s.gpr .r0-1)) 1)
    (readHigh : 1<n → InRegions (s.rd++s.wr) (State.addr (s.gpr .r0-2)) 1)
    (accValue : s.gpr .r2=BitVec.ofNat 32 acc) (accBound : acc<2*divisor)
    (offsetValue : s.gpr .r8=BitVec.ofNat 32 offset) (offsetBound : offset<2*divisor)
    (divValue : s.gpr .r3=BitVec.ofNat 32 divisor) (divBound : 3≤divisor ∧ divisor<8162)
    (invValue : (s.gpr .r4).toNat=inverse) (invCorrect : (divisor*inverse+1)%2^16=0) :
    WP isa trialPairStep s fun t => ∃ a b, a<2*divisor ∧ b<2*divisor ∧
      a*2^16%divisor=(trialDigitNat s.mem (s.gpr .r0) n+acc)%divisor ∧
      b*2^16%divisor=(trialDigitNat s.mem (s.gpr .r0) n+offset)%divisor ∧
      t.gpr .r2=BitVec.ofNat 32 a ∧ t.gpr .r8=BitVec.ofNat 32 b ∧
      t.gpr .r0=s.gpr .r0-BitVec.ofNat 32 (min 2 n) ∧
      t.gpr .r1=BitVec.ofNat 32 (n-min 2 n) ∧ t.z=decide (n≤2) ∧
      t.mem=s.mem ∧ Rest [.r0,.r1,.r2,.r5,.r6,.r7,.r8] s t := by
  unfold trialPairStep
  refine WP.seq (WP.mono (trialDigit_ok s positive fits count readLow readHigh) ?_)
  rintro u ⟨⟨ptr,cnt,word,mem⟩,rest⟩
  have digitValue : (u.gpr .r5).toNat=trialDigitNat s.mem (s.gpr .r0) n := by
    rw [word]
    unfold trialDigitNat
    by_cases last : n=1
    · simp only [last,ite_true,show (0 : BitVec 32)=0#32 from rfl,BitVec.or_zero,Nat.add_zero,BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (s.mem (State.addr (s.gpr .r0-1))).isLt;omega)
    · rw [ite_eq_right last,ite_eq_right last,trialDigit_value]
  have digitBound : trialDigitNat s.mem (s.gpr .r0) n<2^16 := by
    have lo := (s.mem (State.addr (s.gpr .r0-1))).isLt
    have hi := (s.mem (State.addr (s.gpr .r0-2))).isLt
    unfold trialDigitNat
    split <;> omega
  simp only [List.cons_append,List.nil_append]
  refine wp_mov (op2_reg _ _) fun v save => ?_
  have kept : Rest [.r0,.r1,.r2,.r5,.r6,.r7,.r8] s v :=
    (rest.mono (by simp)).trans (save.rest (by simp))
  refine VG.Proof.Bignum.Arm.TrialDivision16.redc_ok
    (by rw [save.other .r5 (by decide)];exact digitValue) digitBound
    ((save.other .r2 (by decide)).trans ((rest.gpr .r2 (by simp)).trans accValue)) accBound
    (by rw [save.other .r4 (by decide),rest.gpr .r4 (by simp)];exact invValue)
    ((save.other .r3 (by decide)).trans ((rest.gpr .r3 (by simp)).trans divValue)) divBound invCorrect ?_
  intro x keepX memX a boundA congA valA
  have xdigit : (x.gpr .r7).toNat=trialDigitNat s.mem (s.gpr .r0) n := by
    rw [keepX.gpr .r7 (by simp),save.gpr]
    exact digitValue
  refine trialPairRedc_ok xdigit digitBound
    ((keepX.gpr .r8 (by simp)).trans ((save.other .r8 (by decide)).trans ((rest.gpr .r8 (by simp)).trans offsetValue))) offsetBound
    (by rw [keepX.gpr .r4 (by simp),save.other .r4 (by decide),rest.gpr .r4 (by simp)];exact invValue)
    ((keepX.gpr .r3 (by simp)).trans ((save.other .r3 (by decide)).trans ((rest.gpr .r3 (by simp)).trans divValue)))
    divBound invCorrect ?_
  intro y keepY memY b boundB congB valB
  refine wp_cmp (op2_imm (by decide)) fun t final flag => WP.block_nil ?_
  refine ⟨a,b,boundA,boundB,congA,congB,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [final.gpr,keepY.gpr .r2 (by simp),valA]
  · rw [final.gpr,valB]
  · rw [final.gpr,keepY.gpr .r0 (by simp),keepX.gpr .r0 (by simp),save.other .r0 (by decide),ptr]
  · rw [final.gpr,keepY.gpr .r1 (by simp),keepX.gpr .r1 (by simp),save.other .r1 (by decide),cnt]
  · rw [flag,keepY.gpr .r1 (by simp),keepX.gpr .r1 (by simp),save.other .r1 (by decide),cnt]
    rw [show (0 : BitVec 32)=0#32 from rfl,BitVec.sub_zero]
    change (BitVec.ofNat 32 (n-min 2 n)==(0 : BitVec 32))=_
    rw [ofNat_beq_zero (by omega : n-min 2 n<2^32)]
    simp only [show n-min 2 n=0 ↔ n≤2 by omega]
  · rw [final.mem,memY,memX,save.mem,mem]
  · exact kept.trans ((keepX.mono (by simp)).trans ((keepY.mono (by simp)).trans (final.rest _)))


end VG.Proof.Ffdh.Arm.ParameterCandidate
