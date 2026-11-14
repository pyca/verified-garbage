module

public import VerifiedGarbage.Proof.P256.Linear.WeakWords
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Arithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `P256.Linear.WeakCore`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.Linear.Weak
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def regs (s : State) : W4 := (s.gpr .x5,s.gpr .x6,s.gpr .x7,s.gpr .x8)
def addCode : List Instr :=
  [.adds .x .x5 .x5 .x9,.adcs .x .x6 .x6 .x10,.adcs .x .x7 .x7 .x11,.adcs .x .x8 .x8 .x12]

theorem addCode_ok (s : State) : WP isa (.block addCode) s fun t =>
    regs t=(addWords (regs s) (s.gpr .x9,s.gpr .x10,s.gpr .x11,s.gpr .x12)).1 ∧
    t.c=(addWords (regs s) (s.gpr .x9,s.gpr .x10,s.gpr .x11,s.gpr .x12)).2 ∧ Keeps [.x5,.x6,.x7,.x8] s t := by
  apply WP.of_runBlock
  simp only [regs,addCode,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,BitVec.setWidth_eq,
    ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left',addWords,addCarry,carryOut]
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps

def reduceCode : List Instr :=
  [.movz .x .x17 0 0,.movz .x .x16 1 0,.sub .x .x13 .x17 .x16,
   .csel .x .x3 .x13 .x17,.subs .x .x5 .x5 .x3,
   .lsl .x .x1 .x3 32,.lsr .x .x1 .x1 32,.sbcs .x .x6 .x6 .x1,
   .sbcs .x .x7 .x7 .x17,.lsl .x .x2 .x3 32,.sub .x .x2 .x2 .x3,
   .sbc .x .x8 .x8 .x2]

theorem reduceCode_ok (s : State) : WP isa (.block reduceCode) s fun t =>
    regs t=weakWords (regs s) s.c ∧ Keeps [.x1,.x2,.x3,.x5,.x6,.x7,.x8,.x13,.x16,.x17] s t := by
  apply WP.of_runBlock
  cases hc : s.c <;>
    simp only [regs,reduceCode,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
      RegUpd.gpr_write,RegUpd.c_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
      BitVec.setWidth_eq,show 16*0<64 by decide,show 32<64 by decide,
      ite_true,ite_false,reduceCtorEq,hc,Option.some.injEq,exists_eq_left']
  all_goals
    refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
    · simp only [weakWords,subWords,modulusWords,addCarry,carryOut]
      rfl
    · reg_keeps
end VG.Proof.P256.Linear.Weak

end

end


@[expose] public section

namespace VG.Proof.P256.Linear.Weak
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def reference (o a b : Nat) : List Instr :=
  loads [.x5,.x6,.x7,.x8] a ++ loads [.x9,.x10,.x11,.x12] b ++ addCode ++ reduceCode ++ stores [.x5,.x6,.x7,.x8] o

theorem regs_value (s : State) : regsVal s [.x5,.x6,.x7,.x8]=value (regs s) := by
  simp only [regsVal,value,regs,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]

theorem reference_ok {s : State} {base : Addr} {size o a b : Nat}
    (hs : Scr s base size) (ho : o+32≤size) (ha : a+32≤size) (hb : b+32≤size)
    (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (haP : wordsVal s.mem base a 4<p) (hbP : wordsVal s.mem base b 4<p) :
    WP isa (.block (reference o a b)) s fun t =>
      KeepRegs (clob 4) s t ∧ VG.Proof.Mont.Outside base o 32 s.mem t.mem ∧
      wordsVal t.mem base o 4%p=(wordsVal s.mem base a 4+wordsVal s.mem base b 4)%p := by
  unfold reference
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  rw [loads_eq]
  refine WP.mono (loadsR_ok [.x5,.x6,.x7,.x8] hs.ptr ha ha8 (by decide) (by decide)) fun s1 ⟨e1,k1,_⟩ => ?_
  rw [WP.block_append_iff]
  rw [loads_eq]
  refine WP.mono (loadsR_ok [.x9,.x10,.x11,.x12] (hs.of_keeps k1 (by decide)).ptr hb hb8 (by decide) (by decide)) fun s2 ⟨e2,k2,_⟩ => ?_
  have v1 : value (regs s2)=wordsVal s.mem base a 4 := by
    rw [←regs_value]
    calc
      regsVal s2 [.x5,.x6,.x7,.x8]=regsVal s1 [.x5,.x6,.x7,.x8] := by
        apply regsVal_congr
        intro r hr
        apply k2.gpr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide
      _ = _ := e1
  have v2 : value (s2.gpr .x9,s2.gpr .x10,s2.gpr .x11,s2.gpr .x12)=wordsVal s.mem base b 4 := by
    rw [k1.mem] at e2
    have hh : value (s2.gpr .x9,s2.gpr .x10,s2.gpr .x11,s2.gpr .x12)=regsVal s2 [.x9,.x10,.x11,.x12] := by
      simp only [regsVal,value,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
    exact hh.trans e2
  rw [WP.block_append_iff]
  refine WP.mono (addCode_ok s2) fun s3 ⟨e3,c3,k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduceCode_ok s3) fun s4 ⟨e4,k4⟩ => ?_
  have kk : Keeps (clob 4) s s4 := (k1.mono (by decide)).trans ((k2.mono (by decide)).trans ((k3.mono (by decide)).trans (k4.mono (by decide))))
  refine WP.mono (stores_ok [.x5,.x6,.x7,.x8] (hs.of_keeps kk (by decide)) ho ho8 (by decide)) fun t ⟨et,kt,ot⟩ => ?_
  change wordsVal t.mem base o 4=regsVal s4 [.x5,.x6,.x7,.x8] at et
  change VG.Proof.Mont.Outside base o 32 s4.mem t.mem at ot
  refine ⟨(Keeps.regs kk).trans (kt.mono (by regions_sub)),?_,?_⟩
  · simpa only [kk.mem] using ot
  · rw [et,regs_value,e4,e3,c3]
    have he := weakWords_mod (regs s2) (s2.gpr .x9,s2.gpr .x10,s2.gpr .x11,s2.gpr .x12)
      (by rw [v1]; exact haP) (by rw [v2]; exact hbP)
    simpa only [v1,v2] using he
end VG.Proof.P256.Linear.Weak
