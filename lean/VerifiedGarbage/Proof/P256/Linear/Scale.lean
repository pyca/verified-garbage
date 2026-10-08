import VerifiedGarbage.Proof.P256.Linear.Words
import VerifiedGarbage.Impl.P256.Linear

namespace VG.Proof.P256.Linear
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Proof.Ed25519
open VG.Proof.P256.VerifySparse (four)

def shift3 : List Instr :=
  [.lsl .x .x3 .x9 3,.extr .x .x4 .x10 .x9 61,
   .extr .x .x5 .x11 .x10 61,.extr .x .x6 .x12 .x11 61,.lsr .x .x7 .x12 61]

theorem shift3_ok (s : State) :
    WP isa (.block shift3) s fun t =>
      regsVal t [.x3,.x4,.x5,.x6,.x7]=8*regsVal s [.x9,.x10,.x11,.x12] ∧
      Keeps [.x3,.x4,.x5,.x6,.x7] s t := by
  apply WP.of_runBlock
  simp only [shift3,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 3<64 by decide,show 61<64 by decide,ite_true,RegUpd.gpr_write,
    BitVec.setWidth_eq,reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun q hq => ?_,rfl,rfl,rfl,rfl⟩
  · have h := leftShift_value 3 (Or.inr (Or.inr rfl)) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) (s.gpr .x12)
    simp only [regsVal,Nat.mul_zero,Nat.add_zero,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,BitVec.setWidth_eq]
    simp only [five,four,show 64-3=61 from rfl] at h
    omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
    simp only [RegUpd.gpr_write,hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1,hq.2.2.2.2,ite_false]

def addAcc (x y z w v : Reg) : List Instr :=
  [.adds .x .x3 .x3 x,.adcs .x .x4 .x4 y,.adcs .x .x5 .x5 z,
   .adcs .x .x6 .x6 w,.adc .x .x7 .x7 v]

theorem addAcc_ok (s : State) (x y z w v : Reg)
    (hf : ∀r∈[x,y,z,w,v],r∉[Reg.x3,.x4,.x5,.x6,.x7]) :
    WP isa (.block (addAcc x y z w v)) s fun t =>
      regsVal t [.x3,.x4,.x5,.x6,.x7]=
        (regsVal s [.x3,.x4,.x5,.x6,.x7]+regsVal s [x,y,z,w,v])%2^320 ∧
      Keeps [.x3,.x4,.x5,.x6,.x7] s t := by
  have hy := hf y (by simp)
  have hz := hf z (by simp)
  have hw := hf w (by simp)
  have hv := hf v (by simp)
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hy hz hw hv
  apply WP.of_runBlock
  simp only [addAcc,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    hy.1,hz.1,hz.2.1,hw.1,hw.2.1,hw.2.2.1,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,
    BitVec.setWidth_eq,reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun q hq => ?_,rfl,rfl,rfl,rfl⟩
  · have h := addFive_value (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
      (s.gpr x) (s.gpr y) (s.gpr z) (s.gpr w) (s.gpr v)
    simp only [regsVal,Nat.mul_zero,Nat.add_zero,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
      reduceCtorEq,ite_false,ite_true,BitVec.setWidth_eq]
    simp only [five_eq,Word64.addCarry,Word64.carryOut,Size.bits] at h ⊢
    refine Eq.trans ?_ h
    rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
    simp only [RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
      hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1,hq.2.2.2.2,ite_false]


def shift1 : List Instr :=
  [.lsl .x .x1 .x9 1,.extr .x .x2 .x10 .x9 63,
   .extr .x .x8 .x11 .x10 63,.extr .x .x13 .x12 .x11 63,.lsr .x .x16 .x12 63]

theorem shift1_ok (s : State) :
    WP isa (.block shift1) s fun t =>
      regsVal t [.x1,.x2,.x8,.x13,.x16]=2*regsVal s [.x9,.x10,.x11,.x12] ∧
      Keeps [.x1,.x2,.x8,.x13,.x16] s t := by
  apply WP.of_runBlock
  simp only [shift1,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 1<64 by decide,show 63<64 by decide,ite_true,RegUpd.gpr_write,
    BitVec.setWidth_eq,reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun q hq => ?_,rfl,rfl,rfl,rfl⟩
  · have h := leftShift_value 1 (Or.inl rfl) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) (s.gpr .x12)
    simp only [regsVal,Nat.mul_zero,Nat.add_zero,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,BitVec.setWidth_eq]
    simp only [five,four,show 64-1=63 from rfl] at h
    omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
    simp only [RegUpd.gpr_write,hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1,hq.2.2.2.2,ite_false]

def addTriple : List Instr :=
  [.adds .x .x9 .x9 .x1,.adcs .x .x10 .x10 .x2,.adcs .x .x11 .x11 .x8,
   .adcs .x .x12 .x12 .x13,.adc .x .x16 .x16 .x17]

theorem addTriple_ok (s : State) (hz : s.gpr .x17=0) :
    WP isa (.block addTriple) s fun t =>
      regsVal t [.x9,.x10,.x11,.x12,.x16]=
        (regsVal s [.x9,.x10,.x11,.x12]+regsVal s [.x1,.x2,.x8,.x13,.x16])%2^320 ∧
      Keeps [.x9,.x10,.x11,.x12,.x16] s t := by
  apply WP.of_runBlock
  simp only [addTriple,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,hz,
    BitVec.setWidth_eq,reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun q hq => ?_,rfl,rfl,rfl,rfl⟩
  · have h := addFive_value (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) (s.gpr .x12) (s.gpr .x16)
      (s.gpr .x1) (s.gpr .x2) (s.gpr .x8) (s.gpr .x13) 0
    have hsum : five (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) (s.gpr .x12) (s.gpr .x16)+
        five (s.gpr .x1) (s.gpr .x2) (s.gpr .x8) (s.gpr .x13) 0=
        regsVal s [.x9,.x10,.x11,.x12]+regsVal s [.x1,.x2,.x8,.x13,.x16] := by
      simp only [five,four,regsVal,show (0:BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero]
      omega
    rw [hsum] at h
    simp only [regsVal,Nat.mul_zero,Nat.add_zero,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
      reduceCtorEq,ite_false,ite_true,BitVec.setWidth_eq]
    simp only [five_eq,Word64.addCarry,Word64.carryOut,Size.bits,
      regsVal,Nat.mul_zero,Nat.add_zero] at h ⊢
    refine Eq.trans ?_ h
    rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
    simp only [RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
      hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1,hq.2.2.2.2,ite_false]

def shift2 : List Instr :=
  [.extr .x .x16 .x16 .x12 62,.extr .x .x13 .x12 .x11 62,
   .extr .x .x8 .x11 .x10 62,.extr .x .x2 .x10 .x9 62,.lsl .x .x1 .x9 2]

theorem shift2_ok (s : State) (he : (s.gpr .x16).toNat<2^62) :
    WP isa (.block shift2) s fun t =>
      regsVal t [.x1,.x2,.x8,.x13,.x16]=4*regsVal s [.x9,.x10,.x11,.x12,.x16] ∧
      Keeps [.x1,.x2,.x8,.x13,.x16] s t := by
  apply WP.of_runBlock
  simp only [shift2,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 2<64 by decide,show 62<64 by decide,ite_true,RegUpd.gpr_write,
    BitVec.setWidth_eq,reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun q hq => ?_,rfl,rfl,rfl,rfl⟩
  · have h := leftShiftFive2_value (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) (s.gpr .x12) (s.gpr .x16) he
    simp only [regsVal,Nat.mul_zero,Nat.add_zero,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,BitVec.setWidth_eq]
    simp only [five_eq] at h
    exact h
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
    simp only [RegUpd.gpr_write,hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1,hq.2.2.2.2,ite_false]


end VG.Proof.P256.Linear
