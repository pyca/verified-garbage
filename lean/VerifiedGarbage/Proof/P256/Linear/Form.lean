module

public import VerifiedGarbage.Impl.P256.Linear
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.P256.Linear.Arithmetic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Impl.NatPairs
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `P256.Linear.Complement`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.Linear
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

/-- The P-256 prime, as this file's statements name it. -/
abbrev complementP := VG.Spec.P256.curve.p

def complement (b : Nat) : List Instr := (Impl.P256.Linear.linear129 0 0 b).take 18

private def compWords (a b c d : Word) : Word × Word × Word × Word :=
  let c0 := carryOut (-1) (~~~a) true
  let c1 := carryOut 0xffffffff (~~~b) c0
  let c2 := carryOut 0 (~~~c) c1
  (addCarry (-1) (~~~a) true,addCarry 0xffffffff (~~~b) c0,
    addCarry 0 (~~~c) c1,addCarry 0xffffffff00000001 (~~~d) c2)

private def compValue (a b c d : Word) : Nat :=
  let w := compWords a b c d
  val4 w.1 w.2.1 w.2.2.1 w.2.2.2

private theorem comp_value (a b c d : Word) (h : val4 a b c d<complementP) :
    compValue a b c d=complementP-val4 a b c d := by
  have he := sub4_value (-1) 0xffffffff 0 0xffffffff00000001 a b c d true
  have hl := val4_lt (compWords a b c d).1 (compWords a b c d).2.1
    (compWords a b c d).2.2.1 (compWords a b c d).2.2.2
  have hc : val4 (-1) 0xffffffff 0 0xffffffff00000001=complementP := by decide
  simp only [Bool.toNat_true,Nat.sub_self,Nat.add_zero,hc] at he
  change compValue a b c d+val4 a b c d = _ at he
  change compValue a b c d<2^256 at hl
  have hb := Bool.toNat_le (carryOut 0xffffffff00000001 (~~~d)
    (carryOut 0 (~~~c) (carryOut 0xffffffff (~~~b) (carryOut (-1) (~~~a) true))))
  omega_using [h, he, hl]

private theorem complement_core {s : State} {base : Addr} {size b : Nat}
    (hs : Scr s base size) (hb : b+32≤size) (hb8 : b%8=0)
    :
    WP isa (.block (complement b)) s fun t =>
      (t.gpr .x9,t.gpr .x10,t.gpr .x11,t.gpr .x12)=
        compWords (VG.Proof.Mont.word s.mem base b) (VG.Proof.Mont.word s.mem base (b+8))
          (VG.Proof.Mont.word s.mem base (b+16)) (VG.Proof.Mont.word s.mem base (b+24)) ∧
      t.gpr .x17=0 ∧ Keeps [.x2,.x9,.x10,.x11,.x12,.x17] s t := by
  have h0 := hs.enc8 (d:=b) (by omega_using [hb]) hb8
  have h8 := hs.enc8 (d:=b+8) (by omega_using [hb]) (by omega_using [hb8])
  have h16 := hs.enc8 (d:=b+16) (by omega_using [hb]) (by omega_using [hb8])
  have h24 := hs.enc8 (d:=b+24) (by omega_using [hb]) (by omega_using [hb8])
  have l0 := hs.ld (d:=b) (by omega_using [hb])
  have l8 := hs.ld (d:=b+8) (by omega_using [hb])
  have l16 := hs.ld (d:=b+16) (by omega_using [hb])
  have l24 := hs.ld (d:=b+24) (by omega_using [hb])
  rw [hs.x0] at l0 l8 l16 l24
  apply WP.of_runBlock
  simp only [complement,Impl.P256.Linear.linear129,List.take_succ_cons,List.take_zero,
    runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,Size.bytes,
    RegUpd.gpr_write,RegUpd.c_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.wr_write,
    RegUpd.mem_addWithCarry,RegUpd.rd_addWithCarry,RegUpd.wr_addWithCarry,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,Nat.add_zero,show 16*0<64 by decide,show 16*1<64 by decide,
    show 16*2<64 by decide,show 16*3<64 by decide,
    and_self,ite_true,ite_false,reduceCtorEq,addr,h0,h8,h16,h24,Option.bind_some,
    State.load,hs.x0,l0,l8,l16,l24,Option.map_some,Option.some.injEq,exists_eq_left']
  refine ⟨?_,rfl,?_,rfl,rfl,rfl,rfl⟩
  · rfl
  · reg_keeps

theorem complement_ok {s : State} {base : Addr} {size b : Nat}
    (hs : Scr s base size) (hb : b+32≤size) (hb8 : b%8=0)
    (hB : wordsVal s.mem base b 4<complementP) :
    WP isa (.block (complement b)) s fun t =>
      regsVal t [.x9,.x10,.x11,.x12]=complementP-wordsVal s.mem base b 4 ∧
      t.gpr .x17=0 ∧ Keeps [.x2,.x9,.x10,.x11,.x12,.x17] s t := by
  refine WP.mono (complement_core hs hb hb8) fun t ⟨he,hz,hk⟩ => ⟨?_,hz,hk⟩
  have hv : val4 (VG.Proof.Mont.word s.mem base b) (VG.Proof.Mont.word s.mem base (b+8))
      (VG.Proof.Mont.word s.mem base (b+16)) (VG.Proof.Mont.word s.mem base (b+24)) = wordsVal s.mem base b 4 := by
    simp only [val4,wordsVal,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
  have hc := comp_value (VG.Proof.Mont.word s.mem base b) (VG.Proof.Mont.word s.mem base (b+8))
    (VG.Proof.Mont.word s.mem base (b+16)) (VG.Proof.Mont.word s.mem base (b+24)) (by rw [hv]; exact hB)
  rw [hv] at hc
  have ht : regsVal t [.x9,.x10,.x11,.x12]=val4 (t.gpr .x9) (t.gpr .x10) (t.gpr .x11) (t.gpr .x12) := by
    simp only [regsVal,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
  rw [ht]
  change (let w := (t.gpr .x9,t.gpr .x10,t.gpr .x11,t.gpr .x12); val4 w.1 w.2.1 w.2.2.1 w.2.2.2)=_
  rw [he]
  exact hc

end VG.Proof.P256.Linear

end

end

/-! ### `P256.Linear.Scale`, which only this module used -/

section

@[expose] public section

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
    omega_arith
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
    omega_arith
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
      omega_arith
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

end

end


@[expose] public section

namespace VG.Proof.P256.Linear
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def aRegs : List Reg := [.x1,.x2,.x8,.x9,.x10,.x11,.x12,.x13,.x16]
def formRegs : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x16,.x17]
def tripleA (a : Nat) : List Instr := loads [.x9,.x10,.x11,.x12] a++shift1++addTriple

theorem tripleA_ok {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : a+32≤size) (ha8 : a%8=0) (hz : s.gpr .x17=0) :
    WP isa (.block (tripleA a)) s fun t =>
      regsVal t [.x9,.x10,.x11,.x12,.x16]=3*wordsVal s.mem base a 4 ∧ Keeps aRegs s t := by
  unfold tripleA
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (loads_ok [.x9,.x10,.x11,.x12] hs ha ha8 (by constructor <;> decide)) fun s1 ⟨e1,k1,_⟩ => ?_
  change regsVal s1 [.x9,.x10,.x11,.x12]=wordsVal s.mem base a 4 at e1
  rw [WP.block_append_iff]
  refine WP.mono (shift1_ok s1) fun s2 ⟨e2,k2⟩ => ?_
  have z2 : s2.gpr .x17=0 := by rw [k2.gpr _ (by decide),k1.gpr _ (by decide),hz]
  refine WP.mono (addTriple_ok s2 z2) fun t ⟨e3,k3⟩ => ?_
  have p2 : regsVal s2 [.x9,.x10,.x11,.x12]=regsVal s1 [.x9,.x10,.x11,.x12] :=
    regsVal_congr fun r hr => k2.gpr r (by revert r; decide)
  have hA := wordsVal_lt s.mem base a 4
  rw [p2,e2,e1] at e3
  refine ⟨?_,((k1.mono (by unfold aRegs; sub_regs)).trans
    (k2.mono (by unfold aRegs; sub_regs))).trans (k3.mono (by unfold aRegs; sub_regs))⟩
  rw [e3]
  omega_using [hA]

def times12A (a : Nat) : List Instr := tripleA a++shift2

theorem times12A_ok {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (ha : a+32≤size) (ha8 : a%8=0) (hz : s.gpr .x17=0) :
    WP isa (.block (times12A a)) s fun t =>
      regsVal t [.x1,.x2,.x8,.x13,.x16]=12*wordsVal s.mem base a 4 ∧ Keeps aRegs s t := by
  unfold times12A
  rw [WP.block_append_iff]
  refine WP.mono (tripleA_ok hs ha ha8 hz) fun s1 ⟨e1,k1⟩ => ?_
  have hA := wordsVal_lt s.mem base a 4
  have ht : (s1.gpr .x16).toNat<2^62 := by
    simp only [regsVal,Nat.mul_zero,Nat.add_zero] at e1
    omega_using [e1, hA]
  refine WP.mono (shift2_ok s1 ht) fun t ⟨e2,k2⟩ => ?_
  refine ⟨?_,k1.trans (k2.mono (by unfold aRegs; sub_regs))⟩
  rw [e2,e1]
  omega_using []

def form38 (a b : Nat) : List Instr :=
  complement b++shift3++tripleA a++addAcc .x9 .x10 .x11 .x12 .x16

theorem form38_ok {s : State} {base : Addr} {size a b : Nat}
    (hs : Scr s base size) (ha : a+32≤size) (hb : b+32≤size)
    (ha8 : a%8=0) (hb8 : b%8=0) (hB : wordsVal s.mem base b 4<p) :
    WP isa (.block (form38 a b)) s fun t =>
      regsVal t [.x3,.x4,.x5,.x6,.x7]=
        3*wordsVal s.mem base a 4+8*(p-wordsVal s.mem base b 4) ∧
      t.gpr .x17=0 ∧ Keeps formRegs s t := by
  unfold form38
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (complement_ok hs hb hb8 hB) fun s1 ⟨e1,z1,k1⟩ => ?_
  change regsVal s1 [.x9,.x10,.x11,.x12]=p-wordsVal s.mem base b 4 at e1
  rw [WP.block_append_iff]
  refine WP.mono (shift3_ok s1) fun s2 ⟨e2,k2⟩ => ?_
  rw [WP.block_append_iff]
  have hs2 := (hs.of_keeps k1 (by decide)).of_keeps k2 (by decide)
  refine WP.mono (tripleA_ok hs2 ha ha8 (by rw [k2.gpr _ (by decide),z1])) fun s3 ⟨e3,k3⟩ => ?_
  refine WP.mono (addAcc_ok s3 .x9 .x10 .x11 .x12 .x16 (by decide)) fun t ⟨e4,k4⟩ => ?_
  have p3 : regsVal s3 [.x3,.x4,.x5,.x6,.x7]=regsVal s2 [.x3,.x4,.x5,.x6,.x7] :=
    regsVal_congr fun r hr => k3.gpr r (by revert r; decide)
  rw [k2.mem,k1.mem] at e3
  rw [p3,e3,e2,e1] at e4
  have hA := wordsVal_lt s.mem base a 4
  refine ⟨?_,?_,(((k1.mono (by unfold formRegs; sub_regs)).trans
    (k2.mono (by unfold formRegs; sub_regs))).trans
    (k3.mono (by unfold formRegs aRegs; sub_regs))).trans (k4.mono (by unfold formRegs; sub_regs))⟩
  · rw [e4]
    simp only [p_value] at hB ⊢
    omega_using [hA]
  · rw [k4.gpr _ (by decide),k3.gpr _ (by decide),k2.gpr _ (by decide),z1]

def nineB (b : Nat) : List Instr :=
  complement b++shift3++addAcc .x9 .x10 .x11 .x12 .x17

theorem nineB_ok {s : State} {base : Addr} {size b : Nat}
    (hs : Scr s base size) (hb : b+32≤size) (hb8 : b%8=0) (hB : wordsVal s.mem base b 4<p) :
    WP isa (.block (nineB b)) s fun t =>
      regsVal t [.x3,.x4,.x5,.x6,.x7]=9*(p-wordsVal s.mem base b 4) ∧
      t.gpr .x17=0 ∧ Keeps formRegs s t := by
  unfold nineB
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (complement_ok hs hb hb8 hB) fun s1 ⟨e1,z1,k1⟩ => ?_
  change regsVal s1 [.x9,.x10,.x11,.x12]=p-wordsVal s.mem base b 4 at e1
  rw [WP.block_append_iff]
  refine WP.mono (shift3_ok s1) fun s2 ⟨e2,k2⟩ => ?_
  refine WP.mono (addAcc_ok s2 .x9 .x10 .x11 .x12 .x17 (by decide)) fun t ⟨e3,k3⟩ => ?_
  have z2 : s2.gpr .x17=0 := by rw [k2.gpr _ (by decide),z1]
  have pp : regsVal s2 [.x9,.x10,.x11,.x12,.x17]=regsVal s1 [.x9,.x10,.x11,.x12] := by
    have e : regsVal s2 [.x9,.x10,.x11,.x12]=regsVal s1 [.x9,.x10,.x11,.x12] :=
      regsVal_congr fun r hr => k2.gpr r (by revert r; decide)
    simp only [regsVal,z2,show (0:BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero] at e ⊢
    exact e
  rw [pp,e2,e1] at e3
  refine ⟨?_,by rw [k3.gpr _ (by decide),z2],((k1.mono (by unfold formRegs; sub_regs)).trans
    (k2.mono (by unfold formRegs; sub_regs))).trans (k3.mono (by unfold formRegs; sub_regs))⟩
  rw [e3]
  simp only [p_value] at hB ⊢
  omega_using []

def form129 (a b : Nat) : List Instr := nineB b++times12A a++addAcc .x1 .x2 .x8 .x13 .x16

theorem form129_ok {s : State} {base : Addr} {size a b : Nat}
    (hs : Scr s base size) (ha : a+32≤size) (hb : b+32≤size)
    (ha8 : a%8=0) (hb8 : b%8=0) (hB : wordsVal s.mem base b 4<p) :
    WP isa (.block (form129 a b)) s fun t =>
      regsVal t [.x3,.x4,.x5,.x6,.x7]=
        12*wordsVal s.mem base a 4+9*(p-wordsVal s.mem base b 4) ∧
      t.gpr .x17=0 ∧ Keeps formRegs s t := by
  unfold form129
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (nineB_ok hs hb hb8 hB) fun s1 ⟨e1,z1,k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (times12A_ok (hs.of_keeps k1 (by decide)) ha ha8 z1) fun s2 ⟨e2,k2⟩ => ?_
  refine WP.mono (addAcc_ok s2 .x1 .x2 .x8 .x13 .x16 (by decide)) fun t ⟨e3,k3⟩ => ?_
  have p2 : regsVal s2 [.x3,.x4,.x5,.x6,.x7]=regsVal s1 [.x3,.x4,.x5,.x6,.x7] :=
    regsVal_congr fun r hr => k2.gpr r (by revert r; decide)
  rw [k1.mem] at e2
  rw [p2,e2,e1] at e3
  have hA := wordsVal_lt s.mem base a 4
  refine ⟨?_,by rw [k3.gpr _ (by decide),k2.gpr _ (by decide),z1],
    (k1.trans (k2.mono (by unfold formRegs aRegs; sub_regs))).trans (k3.mono (by unfold formRegs; sub_regs))⟩
  rw [e3]
  simp only [p_value] at hB ⊢
  omega_using [hA]


end VG.Proof.P256.Linear
