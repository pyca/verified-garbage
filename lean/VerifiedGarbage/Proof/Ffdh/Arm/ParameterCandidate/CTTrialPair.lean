module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialSmall
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialPairLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStart
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Both divisibility decisions depend only on the public candidate bytes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

private structure PairOriginalReady (p : TrialData) (s : State) : Prop where
  input : TrialState p s
  pointer : s.gpr .r0=p.dst+BitVec.ofNat 32 p.n
  count : s.gpr .r1=BitVec.ofNat 32 p.n
  acc : s.gpr .r2=0
  divisor : s.gpr .r3=p.prime
  inverse : s.gpr .r4=VG.Proof.RsaKeyGen.ninv p.prime

private structure PairReady (p : TrialData) (s : State) : Prop extends PairOriginalReady p s where
  offset : s.gpr .r8=p.prime-1

private theorem start_ready (p : TrialData) (s : State) (h : TrialState p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart) s (PairOriginalReady p) := by
  refine WP.mono (trialStart_ok s p.dst p.n (h.1.frame.read (by decide)) (h.1.frame.read (by decide))
    (h.1.frame.saved 4 (by decide)) (h.1.frame.saved 12 (by decide))) ?_
  rintro t ⟨⟨ptr,count,acc,prime,inverse,memory⟩,rest⟩
  rw [h.2.1] at prime inverse
  exact ⟨⟨h.1.after_memory memory rest,(rest.gpr .r7 (by simp)).trans h.2.1,
    by rw [memory];exact h.2.2⟩,ptr,count,acc,prime,inverse⟩

private theorem init_ready (p : TrialData) (s : State) (h : PairOriginalReady p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairInit) s (PairReady p) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairInit
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t upd => WP.block_nil ?_
  have rest := upd.rest (by simp : Reg.r8∈[.r8])
  refine ⟨⟨⟨h.input.1.after_memory upd.mem rest,(rest.gpr .r7 (by simp)).trans h.input.2.1,
    by rw [upd.mem];exact h.input.2.2⟩,
    (rest.gpr .r0 (by simp)).trans h.pointer,(rest.gpr .r1 (by simp)).trans h.count,
    (rest.gpr .r2 (by simp)).trans h.acc,(rest.gpr .r3 (by simp)).trans h.divisor,
    (rest.gpr .r4 (by simp)).trans h.inverse⟩,?_⟩
  rw [upd.gpr,VG.Proof.X25519.Arm.dpVal,h.divisor]

private theorem ready_pair {s t : State} (h : Two PairReady s t) : TrialPairLoopPair s t := by
  obtain ⟨p,a,b,_⟩ := h
  have countNat : (s.gpr .r1).toNat=p.n := by
    rw [a.count,BitVec.toNat_ofNat,Nat.mod_eq_of_lt a.input.1.countFits]
  refine ⟨⟨a.pointer.trans b.pointer.symm,a.count.trans b.count.symm,a.acc.trans b.acc.symm,
    a.divisor.trans b.divisor.symm,a.inverse.trans b.inverse.symm,?_,?_,?_,?_⟩,
    a.offset.trans b.offset.symm⟩
  · rw [countNat];exact a.input.1.positive
  · rw [countNat,a.pointer];exact a.input.1.readable
  · rw [countNat,b.pointer];exact b.input.1.readable
  · rw [countNat,a.pointer]
    intro i hi
    exact (a.input.2.2 i hi).trans (b.input.2.2 i hi).symm

private theorem pairFlag_taint : ∃ hint, (VG.Taint.check taint (Taint.ofRegs [.r2,.r3,.r8])
    VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairFlag hint).isSome=true := ⟨_,by taint_decide⟩

theorem trialPair_ct : RelCT isa (Two TrialState)
    VG.Impl.Ffdh.Arm.ParameterCandidate.trialPair (fun _ _ => True) := by
  have start : RelCT isa (Two TrialState) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart)
      (Two PairOriginalReady) :=
    two_post (trialStart_ct.mono (fun _ _ ⟨_,_,_,sp⟩ => sp) (fun _ _ _ => trivial)) start_ready
  have initial : RelCT isa (Two PairOriginalReady) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairInit)
      (Two PairReady) :=
    two_post ((VG.Proof.Bignum.Arm.stackOnly_ct _ (by decide)).mono
      (fun _ _ ⟨_,_,_,sp⟩ => sp) (fun _ _ _ => trivial)) init_ready
  have loop := trialPairLoop_ct.mono (fun _ _ h => ready_pair h) (fun _ _ h => h)
  obtain ⟨hint,checked⟩ := pairFlag_taint
  have flag : RelCT isa (fun s t => s.gpr .r2=t.gpr .r2 ∧ s.gpr .r3=t.gpr .r3 ∧ s.gpr .r8=t.gpr .r8)
      VG.Impl.Ffdh.Arm.ParameterCandidate.trialPairFlag (fun _ _ => True) := by
    refine RelCT.taint (A:=taint) (Taint.ofRegs [.r2,.r3,.r8]) ?_ checked
    intro s t h
    refine Taint.agree_ofRegs ?_
    intro reg hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  exact start.seq (initial.seq (loop.seq flag))

end VG.Proof.Ffdh.Arm.ParameterCandidate
