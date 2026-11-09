module

-- separate module: The fused linear-coefficient fold limb/value equations (cms_fold_words) costs 2.73s of proof versus 1.37s of imports; CmsFold composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsScalar
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsLowAll
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsHigh
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LoadWords
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamValue
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RowMath
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsAndWords
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeFold
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointCarry
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value)

theorem cms_not_value (xs : List Word) : value (xs.map (fun x => ~~~x))+value xs=2^(64*xs.length)-1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,value,List.length_cons,pow64_succ,BitVec.toNat_not]
    have h := congrArg (fun n : Nat => 2^64*n) ih
    simp only [Nat.mul_add] at h
    have hx := x.isLt
    have hp : 0<2^(64*xs.length) := Nat.pow_pos (by decide)
    omega_arith

def cmsComplementValue (m : Mem) (p : Addr) (b : Nat) : Nat :=
  value ((readWords m p b 8).map (fun x => ~~~x))+2^512*(511-(word m p (b+64)).toNat)

def cmsLowProductValue (m : Mem) (p : Addr) (b : Nat) : Nat :=
  value ((readWords m p b 8).map fun x => 9 * (~~~x))+2^512*(9*(511-(word m p (b+64)).toNat))

def cmsHighProductValue (m : Mem) (p : Addr) (b : Nat) : Nat :=
  value ((readWords m p b 8).map fun x => mulHi 9 (~~~x))

theorem cms_complement_value (m : Mem) (p : Addr) (b : Nat) (hb : wordsVal m p b 9<2^521) :
    cmsComplementValue m p b+wordsVal m p b 9=2^521-1 := by
  have hnot := cms_not_value (readWords m p b 8)
  rw [readWords_value,readWords_length] at hnot
  simp only [Nat.reduceMul] at hnot
  have hone : wordsVal m p (b+64) 1=(word m p (b+64)).toNat := by
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  have split := wordsVal_split m p b 8 1
  simp only [Nat.reduceAdd,Nat.reduceMul,hone] at split
  dsimp only [cmsComplementValue]
  omega_using [hb,hnot,split]

theorem cms_product_halves (m : Mem) (p : Addr) (b : Nat) :
    cmsLowProductValue m p b+2^64*cmsHighProductValue m p b=9*cmsComplementValue m p b := by
  have h := product_halves 9 ((readWords m p b 8).map (fun x => ~~~x))
  simp only [List.map_map,Function.comp_def,show (9 : Word).toNat=9 from rfl] at h
  change value ((readWords m p b 8).map fun x => 9 * (~~~x))+
    2^64*value ((readWords m p b 8).map fun x => mulHi 9 (~~~x))=
    9*value ((readWords m p b 8).map (fun x => ~~~x)) at h
  dsimp only [cmsLowProductValue,cmsHighProductValue,cmsComplementValue]
  simp only [Nat.mul_add]
  omega_using [h]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value addWords addWords_value)

theorem cms_high_value (s : State)
    (hb : regsVal s cmsScalarRegs+2^64*regsVal s cmsLowIn<2^576) :
    WP isa (.block cmsHighCode) s fun t =>
      regsVal t cmsScalarRegs=regsVal s cmsScalarRegs+2^64*regsVal s cmsLowIn ∧
      t.gpr .x15=cmsAndWords (cmsMiddleRegs.map t.gpr) ∧ Keeps cmsHighClob s t := by
  refine WP.mono (cms_high_words s) fun t ⟨out,mid,k⟩ => ?_
  have e := addWords_value (cmsHighOut.map s.gpr) (cmsLowIn.map s.gpr) false
    (by simp only [List.length_map,show cmsHighOut.length=8 from by decide,show cmsLowIn.length=8 from by decide])
  rw [←out,value_map_gpr,value_map_gpr,value_map_gpr] at e
  simp only [List.length_map,show cmsHighOut.length=8 from by decide,Nat.reduceMul,Bool.toNat_false,Nat.add_zero] at e
  have split (v : State) : regsVal v cmsScalarRegs=(v.gpr .x3).toNat+2^64*regsVal v cmsHighOut := rfl
  have scaled := congrArg (fun a : Nat => 2^64*a) e
  simp only [Nat.mul_add,←Nat.mul_assoc] at scaled
  have pw : 2^64*2^512=2^576 := by lit_decide
  rw [pw] at scaled
  have full : regsVal t cmsScalarRegs+2^576*(addWords (cmsHighOut.map s.gpr) (cmsLowIn.map s.gpr) false).2.toNat=
      regsVal s cmsScalarRegs+2^64*regsVal s cmsLowIn := by
    rw [split,split,k.gpr .x3 (by decide)]
    omega_using [scaled]
  exact ⟨by omega_using [full,hb],mid,k⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value)

def cmsCombinationClob : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23]

def cmsCombinationCode (a b : Nat) : List Instr := cmsScalarCode a++(cmsLowAllCode b++cmsHighCode)

theorem cms_combination_ok {s : State} {p : Addr} {size a b : Nat}
    (hp : Ptr s .x28 p size) (hA : a+72≤size) (hB : b+72≤size) (ha8 : a%8=0) (hb8 : b%8=0)
    (ha : wordsVal s.mem p a 9<2*(2^521-1)) (hb : wordsVal s.mem p b 9<2^521-1) :
    WP isa (.block (cmsCombinationCode a b)) s fun t =>
      regsVal t cmsScalarRegs=12*wordsVal s.mem p a 9+9*cmsComplementValue s.mem p b ∧
      regsVal t cmsScalarRegs<33*(2^521-1) ∧
      t.gpr .x15=cmsAndWords (cmsMiddleRegs.map t.gpr) ∧ t.gpr .x13=511 ∧
      t.gpr .x1=9 ∧ Keeps cmsCombinationClob s t := by
  rw [cmsCombinationCode,WP.block_append_iff]
  refine WP.mono (cms_scalar_ok hp hA ha8 ha) fun u ⟨eu,_,ku⟩ => ?_
  have hpu := hp.of_keeps ku (by decide)
  have top : (u.gpr .x11).toNat<16384 := by
    have split : regsVal u cmsScalarRegs=regsVal u cmsLowOut+2^512*(u.gpr .x11).toNat := by
      have hr : cmsScalarRegs=cmsLowOut++[.x11] := rfl
      rw [hr,regsVal_append]
      simp only [show cmsLowOut.length=8 from by decide,Nat.reduceMul,regsVal,Nat.mul_zero,Nat.add_zero]
    omega_using [eu,split,ha]
  have bField : wordsVal s.mem p b 9<2^521 := by omega_using [hb]
  have ub : wordsVal u.mem p b 9<2^521 := by rw [ku.mem]; exact bField
  rw [WP.block_append_iff]
  refine WP.mono (cms_low_all_ok hpu hB hb8 top ub) fun v ⟨ev,hv,mv,kv1,kv⟩ => ?_
  rw [ku.mem] at ev hv
  have high : regsVal v cmsLowIn=cmsHighProductValue s.mem p b := by
    have e := congrArg value hv
    rw [value_map_gpr] at e
    exact e
  have halves := cms_product_halves s.mem p b
  have cv := cms_complement_value s.mem p b bField
  have total : regsVal v cmsScalarRegs+2^64*regsVal v cmsLowIn=
      12*wordsVal s.mem p a 9+9*cmsComplementValue s.mem p b := by
    rw [high]
    have ev' : regsVal v cmsScalarRegs=12*wordsVal s.mem p a 9+cmsLowProductValue s.mem p b := by
      dsimp only [cmsLowProductValue]
      omega_using [ev,eu]
    rw [ev']
    omega_using [halves]
  have bound : 12*wordsVal s.mem p a 9+9*cmsComplementValue s.mem p b<33*(2^521-1) := by
    omega_using [ha,cv]
  have fits : regsVal v cmsScalarRegs+2^64*regsVal v cmsLowIn<2^576 := by
    rw [total]
    omega_using [bound]
  refine WP.mono (cms_high_value v fits) fun t ⟨et,mid,kt⟩ => ?_
  rw [total] at et
  exact ⟨et,by rw [et]; exact bound,mid,(kt.gpr .x13 (by decide)).trans mv,
    (kt.gpr .x1 (by decide)).trans kv1,(ku.mono (by decide)).trans
      ((kv.mono (by decide)).trans (kt.mono (by decide)))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field

theorem cms_fold_value {p n : Nat} (hp : 33<p) (hn : n<33*p) :
    n%(p+1)+n/(p+1)<2*p ∧ (n%(p+1)+n/(p+1))%p=n%p := by
  have hq : n/(p+1)<33 := (Nat.div_lt_iff_lt_mul (by omega_arith)).mpr (by omega_arith)
  have hr := Nat.mod_lt n (show 0<p+1 by omega_arith)
  refine ⟨by omega_arith,?_⟩
  have he : n=(n%(p+1)+n/(p+1))+p*(n/(p+1)) := by
    have h := Nat.mod_add_div n (p+1)
    rw [Nat.add_mul,Nat.one_mul] at h
    omega_arith
  exact ((congrArg (fun x => x%p) he).trans (Nat.add_mul_mod_self_left _ _ _)).symm

theorem cms_detect_math {p R v out : Nat} {c : Bool}
    (hR : p+1≤R) (ho : out<R) (he : out+R*c.toNat=(R-(p+1))+v+1) :
    c=decide (p≤v) := by
  cases c
  · simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at he
    symm
    exact decide_eq_false (by omega_arith)
  · simp only [Bool.toNat_true,Nat.mul_one] at he
    symm
    exact decide_eq_true (by omega_arith)

theorem cms_end_carry_math {p n w : Nat} {c : Bool}
    (hp : 33<p) (hn : n<33*p)
    (hc : c=decide (p≤n%(p+1)+n/(p+1)))
    (hw : w=(n%(p+1)+n/(p+1)+c.toNat)%(p+1)) :
    w=n%p ∧ w<p := by
  have hv := cms_fold_value hp hn
  let v := n%(p+1)+n/(p+1)
  have vb : v<2*p := hv.1
  have vm : v%p=n%p := hv.2
  have hc' : c=decide (p≤v) := hc
  have hw' : w=(v+c.toNat)%(p+1) := hw
  by_cases h : p≤v
  · rw [hc',decide_eq_true h] at hw'
    simp only [Bool.toNat_true] at hw'
    have he : v+1=(v-p)+(p+1) := by omega_arith
    have hlt : v-p<p := by omega_arith
    rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega_arith : v-p<p+1)] at hw'
    have vz : v=(v-p)+p := by omega_arith
    have modv : v%p=v-p := by rw [vz,Nat.add_mod_right,Nat.mod_eq_of_lt hlt,Nat.add_sub_cancel]
    exact ⟨hw'.trans (modv.symm.trans vm),by rw [hw']; exact hlt⟩
  · rw [hc',decide_eq_false h] at hw'
    simp only [Bool.toNat_false,Nat.add_zero] at hw'
    have hlt : v<p := by omega_arith
    rw [Nat.mod_eq_of_lt (by omega_arith : v<p+1)] at hw'
    exact ⟨hw'.trans ((Nat.mod_eq_of_lt hlt).symm.trans vm),by rw [hw']; exact hlt⟩

theorem cms_detect_field {F R v out : Nat} {c : Bool}
    (hF : 0<F) (hR : F≤R) (ho : out<R)
    (he : out+R*c.toNat=(R-F)+v+1) : c=decide (F-1≤v) := by
  exact cms_detect_math (p:=F-1) (by simpa only [Nat.sub_add_cancel hF] using hR) ho
    (by simpa only [Nat.sub_add_cancel hF] using he)

theorem cms_sum_mask_math {F R v out : Nat} {c co : Bool}
    (hR : F≤R) (hmod : R%F=0)
    (he : out+R*co.toNat=(R-F)+v+c.toNat) : out%F=(v+c.toNat)%F := by
  have hs : (R-F)%F=0 := (Nat.mod_eq_sub_mod hR).symm.trans hmod
  have em := congrArg (fun n : Nat => n%F) he
  simpa only [Nat.add_mod,Nat.mul_mod,hmod,hs,Nat.zero_mul,Nat.zero_mod,Nat.zero_add,Nat.add_zero,Nat.mod_mod] using em

theorem cms_field_end_carry {F n w : Nat} {c : Bool}
    (hF : 34<F) (hn : n<33*(F-1))
    (hc : c=decide (F-1≤n%F+n/F)) (hw : w=(n%F+n/F+c.toNat)%F) :
    w=n%(F-1) ∧ w<F-1 := by
  have hpos : 0<F := by omega_arith
  exact cms_end_carry_math (p:=F-1) (by omega_arith) hn
    (by simpa only [Nat.sub_add_cancel hpos] using hc)
    (by simpa only [Nat.sub_add_cancel hpos] using hw)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (addWords)

def cmsFoldTop (s : State) : Word := s.gpr .x11 ||| ((0 : Word)-512#64)
def cmsFoldHigh (s : State) : Word := s.gpr .x11 >>> 9

def cmsFoldExtended (s : State) : List Word := cmsLowOut.map s.gpr++[cmsFoldTop s]
def cmsFoldAddend (s : State) : List Word := cmsFoldHigh s::List.replicate 8 0

def cmsFoldDetect (s : State) : Bool := carryOut (cmsFoldTop s) 0
  (carryOut (s.gpr .x15) 0 (carryOut (s.gpr .x3) (cmsFoldHigh s) true))

def cmsFoldSum (s : State) : List Word := (addWords (cmsFoldExtended s) (cmsFoldAddend s) (cmsFoldDetect s)).1

def cmsFoldResult (s : State) : List Word :=
  (cmsFoldSum s).take 8++[(cmsFoldSum s).getD 8 0 &&& (511 : Word)]

def cmsFoldClob : List Reg := [.x0,.x1,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12]

def cmsFoldCode : List Instr := [
  .lsr .x .x12 .x11 9,
  .movz .x .x0 0 0,
  .subImm .x .x0 .x0 512,
  .logic .orr .x .x11 .x11 .x0,
  .subs .x .x0 .x0 .x0,
  .adcs .x .x0 .x3 .x12,
  .movz .x .x1 0 0,
  .adcs .x .x0 .x15 .x1,
  .adcs .x .x0 .x11 .x1,
  .adcs .x .x3 .x3 .x12,
  .adcs .x .x4 .x4 .x1,
  .adcs .x .x5 .x5 .x1,
  .adcs .x .x6 .x6 .x1,
  .adcs .x .x7 .x7 .x1,
  .adcs .x .x8 .x8 .x1,
  .adcs .x .x9 .x9 .x1,
  .adcs .x .x10 .x10 .x1,
  .adc .x .x11 .x11 .x1,
  .logic .and .x .x11 .x11 .x13]

theorem cms_fold_words (s : State) (hm : s.gpr .x13=511) :
    WP isa (.block cmsFoldCode) s fun t =>
      cmsScalarRegs.map t.gpr=cmsFoldResult s ∧ t.gpr .x1=0 ∧ Keeps cmsFoldClob s t := by
  apply WP.of_runBlock
  simp only [cmsFoldCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.mul_zero,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_write,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hm,point_zero_word,self_sub_carry,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · simp only [cmsScalarRegs,cmsFoldResult,cmsFoldSum,cmsFoldExtended,cmsFoldAddend,cmsFoldDetect,cmsFoldTop,cmsFoldHigh,
      cmsLowOut,List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.replicate_succ,List.replicate_zero,
      addWords,addCarry,carryOut,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
      List.take,List.getD,List.getElem?_cons,Size.bits]
    rfl
  · dsimp only [cmsFoldClob]
    reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

end VG.Proof.Mont.AArch64.P521Field
