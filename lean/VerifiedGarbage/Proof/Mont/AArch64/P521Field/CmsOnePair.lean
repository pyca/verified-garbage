module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsComplement
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearPair
public import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def cmsOneFirstArith : List Instr := [
  .sub .x .x0 .x2 .x0,
  .subImm .x .x0 .x0 1,
  .adds .x .x3 .x3 .x0,
  .sbcs .x .x4 .x4 .x1]

theorem cms_one_first_words (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block cmsOneFirstArith) s fun t =>
      t.gpr .x3=addCarry (s.gpr .x3) (~~~s.gpr .x0) false ∧
      t.gpr .x4=addCarry (s.gpr .x4) (~~~s.gpr .x1) (carryOut (s.gpr .x3) (~~~s.gpr .x0) false) ∧
      t.c=carryOut (s.gpr .x4) (~~~s.gpr .x1) (carryOut (s.gpr .x3) (~~~s.gpr .x0) false) ∧
      Keeps [.x0,.x3,.x4] s t := by
  apply WP.of_runBlock
  simp only [cmsOneFirstArith,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hz,cms_complement,
    Option.some.injEq,exists_eq_left']
  refine ⟨by rfl,by rfl,by rfl,⟨?_,?_,?_,?_,?_⟩⟩
  · reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

theorem cms_one_first_value (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block cmsOneFirstArith) s fun t =>
      regsVal t [.x3,.x4]+regsVal s [.x0,.x1]+1=
        regsVal s [.x3,.x4]+2^128*(!t.c).toNat ∧ Keeps [.x0,.x3,.x4] s t := by
  refine WP.mono (cms_one_first_words s hz) fun t ⟨a0,a1,c,k⟩ => ?_
  refine ⟨?_,k⟩
  simp only [regsVal,Nat.mul_zero,Nat.add_zero,a0,a1,c]
  have e0 := sub_borrow (s.gpr .x3) (s.gpr .x0) false
  have e1 := sub_borrow (s.gpr .x4) (s.gpr .x1) (carryOut (s.gpr .x3) (~~~s.gpr .x0) false)
  simp only [Bool.not_false,Bool.toNat_true] at e0
  omega_using [e0,e1]

def cmsOneFirst (b : Nat) : List Instr := twoLoads .x28 .x0 .x1 b++cmsOneFirstArith

theorem cms_one_first_loaded {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+16≤size) (hb8 : b%8=0) (hz : s.gpr .x2=0) :
    WP isa (.block (cmsOneFirst b)) s fun t =>
      regsVal t [.x3,.x4]+wordsVal s.mem p b 2+1=
        regsVal s [.x3,.x4]+2^128*(!t.c).toNat ∧ Keeps [.x0,.x1,.x3,.x4] s t := by
  rw [cmsOneFirst,WP.block_append_iff]
  refine WP.mono (two_loads_ok hp hb hb8 (by decide) (by decide)) fun u ⟨b0,b1,_,ku⟩ => ?_
  have uz : u.gpr .x2=0 := (ku.gpr .x2 (by decide)).trans hz
  refine WP.mono (cms_one_first_value u uz) fun t ⟨e,kt⟩ => ?_
  have out : regsVal u [.x3,.x4]=regsVal s [.x3,.x4] := regsVal_congr fun r h =>
    ku.gpr r ((by decide : ∀r∈[Reg.x3,.x4],r∉[Reg.x0,.x1]) r h)
  rw [out] at e
  simp only [regsVal,Nat.mul_zero,Nat.add_zero,b0,b1] at e
  exact ⟨by simpa only [regsVal,wordsVal,Nat.mul_zero,Nat.add_zero] using e,
    (ku.mono (by decide)).trans (kt.mono (by decide))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def cmsOneR0 : Nat → Reg | 0 => .x5 | 1 => .x7 | _ => .x9
def cmsOneR1 : Nat → Reg | 0 => .x6 | 1 => .x8 | _ => .x10
def cmsOnePrev : Nat → Reg | 0 => .x4 | _ => .x15

def cmsOnePairArith (i : Nat) : List Instr := [
  .sbcs .x (cmsOneR0 i) (cmsOneR0 i) .x0,
  .logic .and .x .x15 (cmsOnePrev i) (cmsOneR0 i),
  .sbcs .x (cmsOneR1 i) (cmsOneR1 i) .x1,
  .logic .and .x .x15 .x15 (cmsOneR1 i)]

def cmsOnePairClob (i : Nat) : List Reg := [.x15,cmsOneR0 i,cmsOneR1 i]
def cmsOneLoadedClob (i : Nat) : List Reg := [.x0,.x1,.x15,cmsOneR0 i,cmsOneR1 i]

theorem cms_one_pair_words (s : State) (i : Nat) (hi : i<3) :
    WP isa (.block (cmsOnePairArith i)) s fun t =>
      t.gpr (cmsOneR0 i)=addCarry (s.gpr (cmsOneR0 i)) (~~~s.gpr .x0) s.c ∧
      t.gpr (cmsOneR1 i)=addCarry (s.gpr (cmsOneR1 i)) (~~~s.gpr .x1)
        (carryOut (s.gpr (cmsOneR0 i)) (~~~s.gpr .x0) s.c) ∧
      t.c=carryOut (s.gpr (cmsOneR1 i)) (~~~s.gpr .x1)
        (carryOut (s.gpr (cmsOneR0 i)) (~~~s.gpr .x0) s.c) ∧
      t.gpr .x15=(s.gpr (cmsOnePrev i)&&&t.gpr (cmsOneR0 i))&&&t.gpr (cmsOneR1 i) ∧ Keeps (cmsOnePairClob i) s t := by
  have hc : i=0 ∨ i=1 ∨ i=2 := by omega_arith
  rcases hc with rfl|rfl|rfl <;> apply WP.of_runBlock <;>
    simp only [cmsOnePairArith,cmsOneR0,cmsOneR1,cmsOnePrev,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_write,RegUpd.c_addWithCarry,
      BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  all_goals
    refine ⟨by rfl,by rfl,by rfl,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
    · dsimp only [cmsOnePairClob,cmsOneR0,cmsOneR1]
      reg_keeps
    · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
    · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
    · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
    · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

theorem cms_one_pair_value (s : State) (i : Nat) (hi : i<3) :
    WP isa (.block (cmsOnePairArith i)) s fun t =>
      regsVal t [cmsOneR0 i,cmsOneR1 i]+regsVal s [.x0,.x1]+(!s.c).toNat=
        regsVal s [cmsOneR0 i,cmsOneR1 i]+2^128*(!t.c).toNat ∧
      t.gpr .x15=(s.gpr (cmsOnePrev i)&&&t.gpr (cmsOneR0 i))&&&t.gpr (cmsOneR1 i) ∧ Keeps (cmsOnePairClob i) s t := by
  refine WP.mono (cms_one_pair_words s i hi) fun t ⟨a0,a1,c,m,k⟩ => ?_
  refine ⟨?_,m,k⟩
  simp only [regsVal,Nat.mul_zero,Nat.add_zero,a0,a1,c]
  have e0 := sub_borrow (s.gpr (cmsOneR0 i)) (s.gpr .x0) s.c
  have e1 := sub_borrow (s.gpr (cmsOneR1 i)) (s.gpr .x1) (carryOut (s.gpr (cmsOneR0 i)) (~~~s.gpr .x0) s.c)
  omega_using [e0,e1]

def cmsOnePair (i b : Nat) : List Instr := twoLoads .x28 .x0 .x1 b++cmsOnePairArith i

theorem cms_one_pair_loaded {s : State} {p : Addr} {size b : Nat} (i : Nat) (hi : i<3)
    (hp : Ptr s .x28 p size) (hb : b+16≤size) (hb8 : b%8=0) :
    WP isa (.block (cmsOnePair i b)) s fun t =>
      regsVal t [cmsOneR0 i,cmsOneR1 i]+wordsVal s.mem p b 2+(!s.c).toNat=
        regsVal s [cmsOneR0 i,cmsOneR1 i]+2^128*(!t.c).toNat ∧
      t.gpr .x15=(s.gpr (cmsOnePrev i)&&&t.gpr (cmsOneR0 i))&&&t.gpr (cmsOneR1 i) ∧ Keeps (cmsOneLoadedClob i) s t := by
  have hc : i=0 ∨ i=1 ∨ i=2 := by omega_arith
  have hf : (∀r∈[cmsOneR0 i,cmsOneR1 i],r∉[Reg.x0,.x1]) ∧ cmsOnePrev i∉[Reg.x0,.x1] ∧
      (∀r∈[Reg.x0,.x1],r∈cmsOneLoadedClob i) ∧ (∀r∈cmsOnePairClob i,r∈cmsOneLoadedClob i) := by
    rcases hc with rfl|rfl|rfl <;> decide
  rw [cmsOnePair,WP.block_append_iff]
  refine WP.mono (two_loads_ok hp hb hb8 (by decide) (by decide)) fun u ⟨b0,b1,cu,ku⟩ => ?_
  refine WP.mono (cms_one_pair_value u i hi) fun t ⟨e,m,kt⟩ => ?_
  have out : regsVal u [cmsOneR0 i,cmsOneR1 i]=regsVal s [cmsOneR0 i,cmsOneR1 i] := regsVal_congr fun r h => ku.gpr r (hf.1 r h)
  rw [out,cu] at e
  rw [ku.gpr (cmsOnePrev i) hf.2.1] at m
  simp only [regsVal,Nat.mul_zero,Nat.add_zero,b0,b1] at e
  exact ⟨by simpa only [regsVal,wordsVal,Nat.mul_zero,Nat.add_zero] using e,m,
    (ku.mono hf.2.2.1).trans (kt.mono hf.2.2.2)⟩

end VG.Proof.Mont.AArch64.P521Field
