module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Public division by five determines the exact fixed comb schedule. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest)

theorem combRowsStep_ok (s : State) {m : Nat} (large : 5≤m) (fit : m<2^32)
    (value : s.gpr .r3=BitVec.ofNat 32 m) (zero : s.gpr .r2=0) :
    WP isa (.block rowsStep) s fun t =>
      (t.gpr .r3=BitVec.ofNat 32 (m-5) ∧ t.gpr .r6=s.gpr .r6+1 ∧
        t.gpr .r7=(if 5≤m-5 then 1 else 0) ∧ t.z=decide (m-5<5) ∧ t.mem=s.mem) ∧
      Rest [.r3,.r6,.r7] s t := by
  have sub : BitVec.ofNat 32 m - 5 = BitVec.ofNat 32 (m-5) := by
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) large
  have val : (BitVec.ofNat 32 (m-5)).toNat=m-5 := by
    exact Nat.mod_eq_of_lt (by omega)
  refine withRest (c := .block rowsStep) [.r3,.r6,.r7] ?_ (by
    intro r hr i hi
    simp only [instrs,rowsStep,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp [clobbers,dstOf] at * <;> grind) rfl
  unfold rowsStep
  ffrun [value,zero,sub,val]
  by_cases next : 5≤m-5
  · have last : ¬m-5<5 := by omega
    simp only [show (5 : BitVec 32).toNat=5 from rfl,
      next,last,ite_true,decide_true,decide_false]
    decide
  · have last : m-5<5 := by omega
    simp only [show (5 : BitVec 32).toNat=5 from rfl,
      next,last,ite_false,decide_true,decide_false]
    decide

theorem combRowsLoop_ok (s : State) {N : Nat} (positive : 0<N) (fit : N+4<2^32)
    (value : s.gpr .r3=BitVec.ofNat 32 (N+4)) (zero : s.gpr .r2=0) (start : s.gpr .r6=0) :
    WP isa (.loop (.block rowsStep) .ne) s fun t =>
      t.gpr .r6=BitVec.ofNat 32 ((N+4)/5) ∧ t.mem=s.mem ∧ Rest [.r3,.r6,.r7] s t := by
  let I := fun k t => ∃ i : Nat, 5≤k ∧ k≤N+4 ∧ k+5*i=N+4 ∧
    t.gpr .r3=BitVec.ofNat 32 k ∧ t.gpr .r6=BitVec.ofNat 32 i ∧ t.gpr .r2=0 ∧
    t.mem=s.mem ∧ Rest [.r3,.r6,.r7] s t
  refine WP.loop (M := isa) I ?_ (N+4) s ?_
  · intro k u hu
    obtain ⟨i,large,bound,parts,r3,r6,r2,memU,restU⟩ := hu
    refine WP.mono (combRowsStep_ok u large (by omega) r3 r2) ?_
    rintro v ⟨⟨r3V,r6V,_r7V,zeroV,memV⟩,restV⟩
    have count : v.gpr .r6=BitVec.ofNat 32 (i+1) := by
      rw [r6V,r6]
      change BitVec.ofNat 32 i + BitVec.ofNat 32 1 = _
      exact (BitVec.ofNat_add _ _).symm
    by_cases last : k-5<5
    · left
      refine ⟨?_,?_,memV.trans memU,restU.trans restV⟩
      · change some (!v.z)=some false
        simp only [zeroV,last,decide_true,Bool.not_true]
      · rw [count,show i+1=(N+4)/5 by omega]
    · right
      refine ⟨?_,k-5,by omega,i+1,by omega,by omega,by omega,r3V,count,?_,memV.trans memU,restU.trans restV⟩
      · change some (!v.z)=some true
        simp only [zeroV,last,decide_false,Bool.not_false]
      · exact (restV.gpr .r2 (by simp)).trans r2
  · exact ⟨0,by omega,by omega,by omega,value,start,zero,rfl,Rest.refl _ _⟩

theorem combRowsCount_ok (s : State) {base : BitVec 32} {len N : Nat}
    (locals : Locals base len s) (positive : 0<N) (fit : N+4<2^32)
    (value : s.gpr .r1=BitVec.ofNat 32 N) :
    WP isa rowsCount s fun t =>
      t.gpr .r6=BitVec.ofNat 32 (VG.Spec.Rsa.FixedBaseComb.rows N) ∧
      t.mem=s.mem.writeW (off (State.addr s.sp) 44) (BitVec.ofNat 32 (VG.Spec.Rsa.FixedBaseComb.rows N)) ∧
      Frame [⟨off (State.addr s.sp) 44,4⟩] s.mem t.mem ∧ Rest [.r2,.r3,.r6,.r7,.r12] s t := by
  have init : WP isa (.block [.dp .add .r3 .r1 (.imm 4),.mov .r6 (.imm 0),.mov .r2 (.imm 0)]) s fun u =>
      (u.gpr .r3=BitVec.ofNat 32 (N+4) ∧ u.gpr .r6=0 ∧ u.gpr .r2=0 ∧ u.mem=s.mem) ∧
      Rest [.r2,.r3,.r6] s u := by
    refine withRest (c := .block [.dp .add .r3 .r1 (.imm 4),.mov .r6 (.imm 0),.mov .r2 (.imm 0)])
      [.r2,.r3,.r6] ?_ (by
        intro r hr i hi
        simp only [instrs,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl <;> simp [clobbers,dstOf] at * <;> grind) rfl
    ffrun [value]
    exact (BitVec.ofNat_add N 4).symm
  rw [rowsCount,WP.seq_iff]
  refine WP.mono init ?_
  rintro u ⟨⟨r3,r6,r2,memU⟩,restU⟩
  rw [WP.seq_iff]
  refine WP.mono (combRowsLoop_ok u positive fit r3 r2 r6) ?_
  rintro v ⟨count,memV,restV⟩
  have rest : Rest [.r2,.r3,.r6,.r7,.r12] s v :=
    (restU.mono (by simp)).trans (restV.mono (by simp))
  have equal : (N+4)/5=VG.Spec.Rsa.FixedBaseComb.rows N := by
    unfold VG.Spec.Rsa.FixedBaseComb.rows VG.Spec.Rsa.FixedBaseComb.teeth
    omega
  rw [equal] at count
  refine WP.mono (localStore_ok v .r6 (locals.after rest) (by decide : 44+4≤72) (by decide)) ?_
  rintro t ⟨memT,frameT,restT⟩
  rw [rest.sp,memV,memU,count] at memT
  rw [rest.sp,memV,memU] at frameT
  exact ⟨(restT.gpr .r6 (by simp)).trans count,memT,frameT,
    rest.trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm
