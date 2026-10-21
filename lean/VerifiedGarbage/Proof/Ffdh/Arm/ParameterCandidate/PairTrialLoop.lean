module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairTrialStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialMath
import VerifiedGarbage.Proof.Framework.Omega

/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate

theorem trialPairLoop_ok (s : State) {n divisor inverse initialA initialB : Nat}
    (positive : 0<n) (fits : n<2^32)
    (count : s.gpr .r1=BitVec.ofNat 32 n) (read : TrialReadable s (s.gpr .r0) n)
    (accA : s.gpr .r2=BitVec.ofNat 32 initialA) (boundA : initialA<2*divisor)
    (accB : s.gpr .r8=BitVec.ofNat 32 initialB) (boundB : initialB<2*divisor)
    (divValue : s.gpr .r3=BitVec.ofNat 32 divisor) (divBound : 3≤divisor ∧ divisor<8162)
    (invValue : (s.gpr .r4).toNat=inverse) (invCorrect : (divisor*inverse+1)%2^16=0) :
    WP isa (.loop trialPairStep .ne) s fun t => ∃ a b j, a<2*divisor ∧ b<2*divisor ∧
      t.gpr .r2=BitVec.ofNat 32 a ∧ t.gpr .r8=BitVec.ofNat 32 b ∧
      a*2^(16*j)%divisor=(initialA+trialValue s.mem (s.gpr .r0) n)%divisor ∧
      b*2^(16*j)%divisor=(initialB+trialValue s.mem (s.gpr .r0) n)%divisor ∧
      t.gpr .r1=0 ∧ t.mem=s.mem ∧ Rest [.r0,.r1,.r2,.r5,.r6,.r7,.r8] s t := by
  let regs : List Reg := [.r0,.r1,.r2,.r5,.r6,.r7,.r8]
  let originalA := initialA+trialValue s.mem (s.gpr .r0) n
  let originalB := initialB+trialValue s.mem (s.gpr .r0) n
  let inv := fun k t => ∃ j a b, 0<k ∧ k<2^32 ∧ TrialReadable t (t.gpr .r0) k ∧
    t.gpr .r1=BitVec.ofNat 32 k ∧ a<2*divisor ∧ b<2*divisor ∧
    t.gpr .r2=BitVec.ofNat 32 a ∧ t.gpr .r8=BitVec.ofNat 32 b ∧
    (a+trialValue t.mem (t.gpr .r0) k)*2^(16*j)%divisor=originalA%divisor ∧
    (b+trialValue t.mem (t.gpr .r0) k)*2^(16*j)%divisor=originalB%divisor ∧
    t.mem=s.mem ∧ Rest regs s t
  refine WP.loop (M:=isa) inv ?_ n s ?_
  · intro k u h
    obtain ⟨j,a,b,kp,kfit,readable,cnt,ab,bb,av,bv,congA,congB,memory,rest⟩ := h
    refine WP.mono (trialPairStep_ok u kp kfit cnt (readable.low kp) (fun h => readable.high h)
      av ab bv bb ((rest.gpr .r3 (by simp [regs])).trans divValue) divBound
      (by rw [rest.gpr .r4 (by simp [regs])];exact invValue) invCorrect) ?_
    rintro t ⟨a',b',ab',bb',stepA,stepB,av',bv',ptr,cnt',flag,mem,keep⟩
    have congruenceA : (a'+trialValue t.mem (t.gpr .r0) (k-min 2 k))*
        2^(16*(j+1))%divisor=originalA%divisor := by
      rw [trialValue_step u.mem (u.gpr .r0) kp] at congA
      rw [mem,ptr]
      exact trialRemaining_congruence stepA congA
    have congruenceB : (b'+trialValue t.mem (t.gpr .r0) (k-min 2 k))*
        2^(16*(j+1))%divisor=originalB%divisor := by
      rw [trialValue_step u.mem (u.gpr .r0) kp] at congB
      rw [mem,ptr]
      exact trialRemaining_congruence stepB congB
    have nextRead : TrialReadable t (t.gpr .r0) (k-min 2 k) := by
      rw [ptr]
      exact readable.advance keep (Nat.min_le_right 2 k)
    have kept : Rest regs s t := rest.trans keep
    by_cases last : k≤2
    · have remZero : k-min 2 k=0 := by omega
      left
      refine ⟨?_,a',b',j+1,ab',bb',av',bv',?_,?_,?_,mem.trans memory,kept⟩
      · change some (!t.z)=some false
        simp only [flag,last,decide_true,Bool.not_true]
      · simpa only [remZero,trialValue,Nat.add_zero] using congruenceA
      · simpa only [remZero,trialValue,Nat.add_zero] using congruenceB
      · rw [cnt',remZero];rfl
    · right
      refine ⟨?_,k-min 2 k,by omega,j+1,a',b',by omega,by omega,nextRead,cnt',ab',bb',av',bv',
        congruenceA,congruenceB,mem.trans memory,kept⟩
      change some (!t.z)=some true
      simp only [flag,last,decide_false,Bool.not_false]
  · refine ⟨0,initialA,initialB,positive,fits,read,count,boundA,boundB,accA,accB,?_,?_,rfl,Rest.refl _ _⟩
    all_goals simp only [Nat.mul_zero,Nat.pow_zero,Nat.mul_one];rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
