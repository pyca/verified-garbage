module

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulFirst
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearMask
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsPrefix
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LoadWords
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsComplement
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsChainMath
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Mont.AArch64.P521Field.CmsAndWords`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64

theorem cms_carry_zero (x : Word) (c : Bool) : carryOut x 0 c=(decide (x=BitVec.allOnes 64) && c) := by
  have he : x=BitVec.allOnes 64 ↔ x.toNat=2^64-1 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
  cases c
  · simp only [Bool.and_false,carryOut,Bool.toNat_false,show (0 : Word).toNat=0 from rfl,Nat.add_zero,decide_eq_false_iff_not]
    exact Nat.not_le.mpr x.isLt
  · simp only [Bool.and_true,carryOut,Bool.toNat_true,show (0 : Word).toNat=0 from rfl,Nat.add_zero]
    apply decide_eq_decide.mpr
    rw [he]
    have hx := x.isLt
    omega_arith

theorem cms_and_carry (a b : Word) (c : Bool) : carryOut (a&&&b) 0 c=carryOut b 0 (carryOut a 0 c) := by
  rw [cms_carry_zero,cms_carry_zero,cms_carry_zero]
  simp only [BitVec.and_eq_allOnes_iff,Bool.decide_and,Bool.and_assoc]
  exact Bool.and_left_comm _ _ _

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64
open VG.Proof.Mont.AArch64.P521Square (addWords)

def cmsAndWords : List Word → Word
  | [] => BitVec.allOnes 64
  | a::xs => a&&&cmsAndWords xs

theorem cms_allOnes_carry (c : Bool) : carryOut (BitVec.allOnes 64) 0 c=c := by
  rw [cms_carry_zero]
  simp only [decide_true,Bool.true_and]

theorem cms_carry_tail (xs : List Word) (top : Word) (c : Bool) :
    (addWords (xs++[top]) (List.replicate (xs.length+1) 0) c).2=
      carryOut top 0 (carryOut (cmsAndWords xs) 0 c) := by
  induction xs generalizing c with
  | nil =>
    simp only [List.nil_append,List.length_nil,Nat.zero_add,List.replicate_succ,List.replicate_zero,addWords,cmsAndWords,cms_allOnes_carry]
  | cons a xs ih =>
    simp only [List.cons_append,List.length_cons,List.replicate_succ,addWords,cmsAndWords]
    rw [←List.replicate_succ,ih,cms_and_carry]

theorem cms_compressed_carry (lo h top : Word) (xs : List Word) (c : Bool) :
    (addWords (lo::(xs++[top])) (h::List.replicate (xs.length+1) 0) c).2=
      carryOut top 0 (carryOut (cmsAndWords xs) 0 (carryOut lo h c)) := by
  simp only [addWords]
  exact cms_carry_tail xs top (carryOut lo h c)

end VG.Proof.Mont.AArch64.P521Field

end

end

/-! ### `Mont.AArch64.P521Field.CmsLowAll`, which this module and modules that import it used -/

section

/-! ### `Mont.AArch64.P521Field.CmsTopMath`, which this module and modules that import it used -/

section

/-! Complementing the canonical top nine bits and adding their small product. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64

theorem cms_top_complement (x : Word) (hx : x.toNat<512) : (x^^^511).toNat=511-x.toNat := by
  have he : x=(x.setWidth 9).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    omega_arith
  have hm : (511 : Word)=(BitVec.allOnes 9).setWidth 64 := rfl
  rw [he,hm,←BitVec.setWidth_xor,BitVec.xor_allOnes]
  simp only [BitVec.toNat_setWidth,BitVec.toNat_not]
  omega_arith

theorem cms_top_add_math (a x : Word) (c : Bool) (ha : a.toNat<16384) (hx : x.toNat<512) :
    (addCarry a (9*(x^^^511)) c).toNat=a.toNat+9*(511-x.toNat)+c.toNat := by
  have hm : ((9 : Word)*(x^^^511)).toNat=9*(511-x.toNat) := by
    rw [BitVec.toNat_mul,show (9 : Word).toNat=9 from rfl,cms_top_complement x hx]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have hc : carryOut a (9*(x^^^511)) c=false := by
    simp only [carryOut,hm,decide_eq_false_iff_not]
    have h := Bool.toNat_le c
    omega_arith
  have he := addCarry_value a (9*(x^^^511)) c
  rw [hm,hc] at he
  simpa only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] using he

end VG.Proof.Mont.AArch64.P521Field

end

end

/-! ### `Mont.AArch64.P521Field.CmsLowLoaded`, which this module and modules that import it used -/

section

/-! ### `Mont.AArch64.P521Field.CmsLow`, which this module and modules that import it used -/

section

/-! The first pass adds the low halves of nine times the complemented limbs. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (addWords)

def cmsLowIn : List Reg := [.x20,.x21,.x22,.x23,.x17,.x19,.x2,.x16]
def cmsLowOut : List Reg := [.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10]
def cmsLowClob : List Reg := [.x0,.x1,.x20,.x21,.x22,.x23,.x17,.x19,.x2,.x16,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10]

def cmsLowCode : List Instr := [
  .movz .x .x1 9 0,
  .movz .x .x0 0 0,
  .sub .x .x20 .x0 .x20,
  .subImm .x .x20 .x20 1,
  .mul .x .x0 .x1 .x20,
  .umulh .x20 .x1 .x20,
  .adds .x .x3 .x3 .x0,
  .movz .x .x0 0 0,
  .sub .x .x21 .x0 .x21,
  .subImm .x .x21 .x21 1,
  .mul .x .x0 .x1 .x21,
  .umulh .x21 .x1 .x21,
  .adcs .x .x4 .x4 .x0,
  .movz .x .x0 0 0,
  .sub .x .x22 .x0 .x22,
  .subImm .x .x22 .x22 1,
  .mul .x .x0 .x1 .x22,
  .umulh .x22 .x1 .x22,
  .adcs .x .x5 .x5 .x0,
  .movz .x .x0 0 0,
  .sub .x .x23 .x0 .x23,
  .subImm .x .x23 .x23 1,
  .mul .x .x0 .x1 .x23,
  .umulh .x23 .x1 .x23,
  .adcs .x .x6 .x6 .x0,
  .movz .x .x0 0 0,
  .sub .x .x17 .x0 .x17,
  .subImm .x .x17 .x17 1,
  .mul .x .x0 .x1 .x17,
  .umulh .x17 .x1 .x17,
  .adcs .x .x7 .x7 .x0,
  .movz .x .x0 0 0,
  .sub .x .x19 .x0 .x19,
  .subImm .x .x19 .x19 1,
  .mul .x .x0 .x1 .x19,
  .umulh .x19 .x1 .x19,
  .adcs .x .x8 .x8 .x0,
  .movz .x .x0 0 0,
  .sub .x .x2 .x0 .x2,
  .subImm .x .x2 .x2 1,
  .mul .x .x0 .x1 .x2,
  .umulh .x2 .x1 .x2,
  .adcs .x .x9 .x9 .x0,
  .movz .x .x0 0 0,
  .sub .x .x16 .x0 .x16,
  .subImm .x .x16 .x16 1,
  .mul .x .x0 .x1 .x16,
  .umulh .x16 .x1 .x16,
  .adcs .x .x10 .x10 .x0]

theorem cms_low_words (s : State) :
    WP isa (.block cmsLowCode) s fun t =>
      cmsLowOut.map t.gpr=(addWords (cmsLowOut.map s.gpr) ((cmsLowIn.map s.gpr).map fun x => 9 * (~~~x)) false).1 ∧
      t.c=(addWords (cmsLowOut.map s.gpr) ((cmsLowIn.map s.gpr).map fun x => 9 * (~~~x)) false).2 ∧
      cmsLowIn.map t.gpr=(cmsLowIn.map s.gpr).map (fun x => mulHi 9 (~~~x)) ∧
      t.gpr .x1=9 ∧ Keeps cmsLowClob s t := by
  apply WP.of_runBlock
  simp only [cmsLowCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.mul_zero,Nat.reduceLT,
    ↓RegUpd.gpr_write,↓RegUpd.gpr_addWithCarry,↓RegUpd.c_write,↓RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,
    show BitVec.setWidth 64 (9 : BitVec 16) <<< 0=(9 : BitVec 64) from rfl,
    show BitVec.setWidth 64 (0 : BitVec 16) <<< 0=(0 : BitVec 64) from rfl,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,?_,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · simp only [cmsLowOut,cmsLowIn,List.map_cons,List.map_nil,addWords,addCarry,carryOut,↓RegUpd.gpr_write,↓RegUpd.gpr_addWithCarry,
      BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,cms_complement,Size.bits]
    rfl
  · simp only [cmsLowOut,cmsLowIn,List.map_cons,List.map_nil,addWords,addCarry,carryOut,cms_complement]
    rfl
  · simp only [cmsLowIn,List.map_cons,List.map_nil,mulHi,↓RegUpd.gpr_write,↓RegUpd.gpr_addWithCarry,
      BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,cms_complement]
  · dsimp only [cmsLowClob]
    reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

end VG.Proof.Mont.AArch64.P521Field

end

end

/-! The complemented low-product pass with its original operand reads. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR)
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (addWords)

def cmsLowLoaded (b : Nat) : List Instr := loadsR .x28 cmsLowIn b++cmsLowCode

theorem cms_low_loaded_words {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+64≤size) (hb8 : b%8=0) :
    WP isa (.block (cmsLowLoaded b)) s fun t =>
      cmsLowOut.map t.gpr=(addWords (cmsLowOut.map s.gpr) ((readWords s.mem p b 8).map fun x => 9 * (~~~x)) false).1 ∧
      t.c=(addWords (cmsLowOut.map s.gpr) ((readWords s.mem p b 8).map fun x => 9 * (~~~x)) false).2 ∧
      cmsLowIn.map t.gpr=(readWords s.mem p b 8).map (fun x => mulHi 9 (~~~x)) ∧
      t.gpr .x1=9 ∧ Keeps cmsLowClob s t := by
  rw [cmsLowLoaded,WP.block_append_iff]
  refine WP.mono (loadsR_each cmsLowIn hp (by simpa only [show cmsLowIn.length=8 from by decide] using hb)
    hb8 (by decide) (by decide)) fun u ⟨eu,ku,_⟩ => ?_
  simp only [show cmsLowIn.length=8 from by decide] at eu
  have ou : cmsLowOut.map u.gpr=cmsLowOut.map s.gpr := List.map_congr_left fun r h =>
    ku.gpr r ((by decide : ∀r∈cmsLowOut,r∉cmsLowIn) r h)
  refine WP.mono (cms_low_words u) fun t ⟨ot,ct,ht,k1,kt⟩ => ?_
  rw [eu,ou] at ot ct
  rw [eu] at ht
  exact ⟨ot,ct,ht,k1,(ku.mono (by decide)).trans kt⟩

end VG.Proof.Mont.AArch64.P521Field

end

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def cmsLowTopCode : List Instr := [
  .movz .x .x13 511 0,
  .logic .eor .x .x0 .x0 .x13,
  .mul .x .x0 .x1 .x0,
  .adc .x .x11 .x11 .x0]

theorem cms_low_top_ok (s : State) (hk : s.gpr .x1=9)
    (ha : (s.gpr .x11).toNat<16384) (hx : (s.gpr .x0).toNat<512) :
    WP isa (.block cmsLowTopCode) s fun t =>
      (t.gpr .x11).toNat=(s.gpr .x11).toNat+9*(511-(s.gpr .x0).toNat)+s.c.toNat ∧
      t.gpr .x13=511 ∧ t.c=s.c ∧ Keeps [.x0,.x11,.x13] s t := by
  apply WP.of_runBlock
  simp only [cmsLowTopCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.mul_zero,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.c_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hk,
    show BitVec.setWidth 64 (511 : BitVec 16) <<< 0=(511 : BitVec 64) from rfl,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,True.intro,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · exact cms_top_add_math _ _ _ ha hx
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value addWords addWords_value)

theorem cms_low_loaded_value {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+64≤size) (hb8 : b%8=0) :
    WP isa (.block (cmsLowLoaded b)) s fun t =>
      regsVal t cmsLowOut+2^512*t.c.toNat=regsVal s cmsLowOut+
        value ((readWords s.mem p b 8).map fun x => 9 * (~~~x)) ∧
      cmsLowIn.map t.gpr=(readWords s.mem p b 8).map (fun x => mulHi 9 (~~~x)) ∧
      t.gpr .x1=9 ∧ Keeps cmsLowClob s t := by
  refine WP.mono (cms_low_loaded_words hp hb hb8) fun t ⟨ot,ct,ht,k1,k⟩ => ?_
  have e := addWords_value (cmsLowOut.map s.gpr) ((readWords s.mem p b 8).map fun x => 9 * (~~~x)) false
    (by simp only [List.length_map,show cmsLowOut.length=8 from by decide,readWords_length])
  rw [←ot,←ct,value_map_gpr,value_map_gpr] at e
  simp only [List.length_map,show cmsLowOut.length=8 from by decide,Nat.reduceMul,Bool.toNat_false,Nat.add_zero] at e
  exact ⟨e,ht,k1,k⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value)

def cmsLowAllClob : List Reg := [.x0,.x1,.x20,.x21,.x22,.x23,.x17,.x19,.x2,.x16,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x13]

def cmsLowAllCode (b : Nat) : List Instr := cmsLowLoaded b++
  (([.ldr .x .x0 .x28 (b+64)] : List Instr)++cmsLowTopCode)

theorem cms_low_all_ok {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+72≤size) (hb8 : b%8=0)
    (ha : (s.gpr .x11).toNat<16384) (hx : wordsVal s.mem p b 9<2^521) :
    WP isa (.block (cmsLowAllCode b)) s fun t =>
      regsVal t cmsScalarRegs=regsVal s cmsScalarRegs+
        value ((readWords s.mem p b 8).map fun x => 9 * (~~~x))+
        2^512*(9*(511-(word s.mem p (b+64)).toNat)) ∧
      cmsLowIn.map t.gpr=(readWords s.mem p b 8).map (fun x => mulHi 9 (~~~x)) ∧
      t.gpr .x13=511 ∧ t.gpr .x1=9 ∧ Keeps cmsLowAllClob s t := by
  rw [cmsLowAllCode,WP.block_append_iff]
  refine WP.mono (cms_low_loaded_value hp (by omega_arith) hb8) fun u ⟨eu,hu,ku1,ku⟩ => ?_
  have hpu := hp.of_keeps ku (by decide)
  have hone : wordsVal s.mem p (b+64) 1=(word s.mem p (b+64)).toNat := by
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  have splitWords := wordsVal_split s.mem p b 8 1
  simp only [Nat.reduceAdd,Nat.reduceMul,hone] at splitWords
  have topBound : (word s.mem p (b+64)).toNat<512 := by omega_using [splitWords,hx]
  rw [WP.block_append_iff]
  refine WP.mono (ldR_ok hpu (d:=b+64) (by omega_arith) (by omega_arith) .x0) fun v ⟨av,kv,cv⟩ => ?_
  have v1 : v.gpr .x1=9 := (kv.gpr .x1 (by decide)).trans ku1
  have v11 : v.gpr .x11=s.gpr .x11 := (kv.gpr .x11 (by decide)).trans (ku.gpr .x11 (by decide))
  have bound0 : (v.gpr .x0).toNat<512 := by rw [av,ku.mem]; exact topBound
  refine WP.mono (cms_low_top_ok v v1 (by rw [v11]; exact ha) bound0) fun t ⟨et,mt,_,kt⟩ => ?_
  have tlow : regsVal t cmsLowOut=regsVal u cmsLowOut := regsVal_congr fun r h =>
    (kt.gpr r ((by decide : ∀r∈cmsLowOut,r∉[Reg.x0,.x11,.x13]) r h)).trans
      (kv.gpr r ((by decide : ∀r∈cmsLowOut,r∉[Reg.x0]) r h))
  have thigh : cmsLowIn.map t.gpr=cmsLowIn.map u.gpr := List.map_congr_left fun r h =>
    (kt.gpr r ((by decide : ∀r∈cmsLowIn,r∉[Reg.x0,.x11,.x13]) r h)).trans
      (kv.gpr r ((by decide : ∀r∈cmsLowIn,r∉[Reg.x0]) r h))
  have splitRegs (w : State) : regsVal w cmsScalarRegs=regsVal w cmsLowOut+2^512*(w.gpr .x11).toNat := by
    have hs : cmsScalarRegs=cmsLowOut++[.x11] := rfl
    rw [hs,regsVal_append]
    simp only [show cmsLowOut.length=8 from by decide,Nat.reduceMul,regsVal,Nat.mul_zero,Nat.add_zero]
  rw [v11,av,ku.mem,cv] at et
  refine ⟨?_,thigh.trans hu,mt,(kt.gpr .x1 (by decide)).trans v1,
    (ku.mono (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide)))⟩
  rw [splitRegs,splitRegs,tlow]
  omega_using [eu,et]

end VG.Proof.Mont.AArch64.P521Field

end

end

/-! The high-product pass also collects the middle limbs for carry detection. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (addWords)

def cmsHighOut : List Reg := [.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11]
def cmsMiddleRegs : List Reg := [.x4,.x5,.x6,.x7,.x8,.x9,.x10]
def cmsHighClob : List Reg := [.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x15]

def cmsHighCode : List Instr := [
  .adds .x .x4 .x4 .x20,
  .adcs .x .x5 .x5 .x21,
  .logic .and .x .x15 .x4 .x5,
  .adcs .x .x6 .x6 .x22,
  .logic .and .x .x15 .x15 .x6,
  .adcs .x .x7 .x7 .x23,
  .logic .and .x .x15 .x15 .x7,
  .adcs .x .x8 .x8 .x17,
  .logic .and .x .x15 .x15 .x8,
  .adcs .x .x9 .x9 .x19,
  .logic .and .x .x15 .x15 .x9,
  .adcs .x .x10 .x10 .x2,
  .logic .and .x .x15 .x15 .x10,
  .adc .x .x11 .x11 .x16]

theorem cms_high_words (s : State) :
    WP isa (.block cmsHighCode) s fun t =>
      cmsHighOut.map t.gpr=(addWords (cmsHighOut.map s.gpr) (cmsLowIn.map s.gpr) false).1 ∧
      t.gpr .x15=cmsAndWords (cmsMiddleRegs.map t.gpr) ∧ Keeps cmsHighClob s t := by
  apply WP.of_runBlock
  simp only [cmsHighCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_write,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,?_,?_,?_,?_⟩⟩
  · simp only [cmsHighOut,cmsLowIn,List.map_cons,List.map_nil,addWords,addCarry,carryOut,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Size.bits]
    rfl
  · simp only [cmsMiddleRegs,List.map_cons,List.map_nil,cmsAndWords,RegUpd.gpr_write,
      RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.and_assoc]
  · dsimp only [cmsHighClob]
    reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

end VG.Proof.Mont.AArch64.P521Field
