module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
public import VerifiedGarbage.Proof.P256.Linear.FortyOneWords
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.NatPairs
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Arithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Block

/-! ### `P256.Linear.FortyOneCore`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.Linear.FortyOne
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open Weak (W4 value addWords subWords)

def input (s : State) : W4 := (s.gpr .x1,s.gpr .x2,s.gpr .x3,s.gpr .x4)
def other (s : State) : W4 := (s.gpr .x9,s.gpr .x10,s.gpr .x11,s.gpr .x12)
def output (s : State) : W4 := (s.gpr .x14,s.gpr .x1,s.gpr .x2,s.gpr .x3)

def prefixCode : List Instr :=
  [.movz .x .x17 0 0,.lsl .x .x14 .x1 2,.subs .x .x14 .x14 .x9,
   .extr .x .x1 .x2 .x1 62,.sbcs .x .x1 .x1 .x10,
   .extr .x .x2 .x3 .x2 62,.sbcs .x .x2 .x2 .x11,
   .extr .x .x3 .x4 .x3 62,.sbcs .x .x3 .x3 .x12,
   .lsr .x .x4 .x4 62,.sbc .x .x4 .x4 .x17]

theorem prefix_ok (s : State) : WP isa (.block prefixCode) s fun t =>
    output t=(subWords (shift2 (input s)).1 (other s)).1 ∧
    t.gpr .x4=highWord (shift2 (input s)).2 (subWords (shift2 (input s)).1 (other s)).2 ∧
    t.gpr .x17=0 ∧ Keeps [.x1,.x2,.x3,.x4,.x14,.x17] s t := by
  apply WP.of_runBlock
  simp only [prefixCode,input,other,output,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.c_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,show 16*0<64 by decide,show 2<64 by decide,show 62<64 by decide,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left',
    subWords,shift2,highWord,addCarry,carryOut]
  refine ⟨rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps

def reduce : List Instr :=
  [.movz .x .x16 1 0,.add .x .x5 .x4 .x16,.lsl .x .x8 .x5 32,
   .subs .x .x6 .x17 .x8,.sbcs .x .x7 .x17 .x17,.sbc .x .x8 .x8 .x5,
   .adds .x .x14 .x14 .x5,.adcs .x .x1 .x1 .x6,.adcs .x .x2 .x2 .x7,.adcs .x .x3 .x3 .x8]

theorem reduce_ok (s : State) (hz : s.gpr .x17=0) : WP isa (.block reduce) s fun t =>
    output t=(addWords (output s) (correction (s.gpr .x4+1))).1 ∧
    t.c=(addWords (output s) (correction (s.gpr .x4+1))).2 ∧
    Keeps [.x1,.x2,.x3,.x5,.x6,.x7,.x8,.x14,.x16] s t := by
  apply WP.of_runBlock
  simp only [reduce,output,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,show 16*0<64 by decide,show 32<64 by decide,hz,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left',
    addWords,correction,addCarry,carryOut]
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl,rfl⟩
  reg_keeps

def back : List Instr :=
  [.sbc .x .x5 .x17 .x17,.adds .x .x14 .x14 .x5,
   .lsl .x .x6 .x5 32,.lsr .x .x6 .x6 32,.adcs .x .x1 .x1 .x6,
   .adcs .x .x2 .x2 .x17,.sub .x .x7 .x17 .x6,.adc .x .x3 .x3 .x7]

theorem back_ok (s : State) (hz : s.gpr .x17=0) : WP isa (.block back) s fun t =>
    output t=addBack (output s) s.c ∧ Keeps [.x1,.x2,.x3,.x5,.x6,.x7,.x14] s t := by
  apply WP.of_runBlock
  cases hc : s.c <;>
    simp only [back,output,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
      RegUpd.gpr_write,RegUpd.c_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
      BitVec.setWidth_eq,show 32<64 by decide,hz,hc,
      ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  all_goals
    refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
    · simp only [addBack,addWords,Weak.modulusWords,addCarry,carryOut]
      rfl
    · reg_keeps
end VG.Proof.P256.Linear.FortyOne

end

end

/-! ### `P256.Linear.FortyOneValue`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.Linear.FortyOne
open VG.Proof.Ed25519.Word64
open Weak (W4 value addWords subWords addWords_value subWords_value value_lt)

def result (a b : W4) : W4 :=
  let u:=shift2 a
  let v:=subWords u.1 b
  let q:=quotient u.2 v.2
  let w:=addWords v.1 (correction q)
  addBack w.1 w.2

theorem canonical_nat {a b out : Nat} (hb : b<p)
    (hf : (out:Int)=(4*(a:Int)-(b:Int))%(p:Int)) : out=(4*a+p-b)%p := by
  have he : ((4*a+p-b:Nat):Int)=(4*(a:Int)-(b:Int))+(p:Int) := by omega_using [hb]
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod,he,Int.add_emod_right]
  exact hf

theorem result_value (a b : W4) (ha : value a<p) (hb : value b<p) :
    value (result a b)=(4*value a+p-value b)%p := by
  let u:=shift2 a
  let v:=subWords u.1 b
  let q:=quotient u.2 v.2
  let w:=addWords v.1 (correction q)
  let n : Int := 4*(value a:Int)-(value b:Int)
  have hu := shift2_value a
  have hv := subWords_value u.1 b
  have huv : u.2.toNat<4 := by
    change (a.2.2.2 >>> 62).toNat<4
    have := a.2.2.2.isLt
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    omega_using []
  have hq := quotient_value u.2 v.2 huv
  have hc := Bool.toNat_le v.2
  have hq4 : q.toNat≤4 := by dsimp only [q]; omega_using [huv, hq, hc]
  have hn0 : -(p:Int)≤n := by dsimp only [n]; omega_using [hb]
  have hn1 : n<21*(p:Int) := by dsimp only [n]; omega_using [ha]
  have hvl := value_lt v.1
  have he : n=(value v.1:Int)+(radix:Int)*((q.toNat:Int)-1) := by
    change value u.1+radix*u.2.toNat=4*value a at hu
    change value v.1+value b=value u.1+Weak.R*(1-v.2.toNat) at hv
    change q.toNat=u.2.toNat+v.2.toNat at hq
    dsimp only [n]
    simp only [radix,Weak.R] at hu hv ⊢
    omega_using [hc, hu, hv, hq]
  have hquot : (q.toNat:Int)=n/(radix:Int)+1 := by
    simp only [radix,Weak.R] at he hvl ⊢
    omega_using [hvl, he]
  have hw := addWords_value v.1 (correction q)
  rw [correction_value q hq4] at hw
  have hw' : (value w.1:Int)+(radix:Int)*(w.2.toNat:Int)-radix=
      n-(n/(radix:Int)+1)*(p:Int) := by
    change value w.1+Weak.R*w.2.toNat=value v.1+q.toNat*(radix-p) at hw
    rw [←hquot]
    simp only [radix,Weak.R,p,VG.Spec.P256.p] at hw he ⊢
    omega_using [he, hw]
  have hf := addBack_value w.1 w.2 hn0 hn1 hw'
  change (value (result a b):Int)=n%(p:Int) at hf
  exact canonical_nat hb hf
end VG.Proof.P256.Linear.FortyOne

end

end


@[expose] public section

namespace VG.Proof.P256.Linear.FortyOne
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open Weak (W4 value)

def reference (o a b : Nat) : List Instr :=
  loads [.x1,.x2,.x3,.x4] a ++ loads [.x9,.x10,.x11,.x12] b ++ prefixCode ++ reduce ++ back ++ stores [.x14,.x1,.x2,.x3] o

theorem input_value (s : State) : regsVal s [.x1,.x2,.x3,.x4]=value (input s) := by
  simp only [regsVal,value,input,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
theorem other_value (s : State) : regsVal s [.x9,.x10,.x11,.x12]=value (other s) := by
  simp only [regsVal,value,other,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
theorem output_value (s : State) : regsVal s [.x14,.x1,.x2,.x3]=value (output s) := by
  simp only [regsVal,value,output,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]

theorem reference_ok {s : State} {base : Addr} {size o a b : Nat}
    (hs : Scr s base size) (ho : o+32≤size) (ha : a+32≤size) (hb : b+32≤size)
    (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (haP : wordsVal s.mem base a 4<p) (hbP : wordsVal s.mem base b 4<p) :
    WP isa (.block (reference o a b)) s fun t =>
      KeepRegs (clob 4) s t ∧ VG.Proof.Mont.Outside base o 32 s.mem t.mem ∧
      wordsVal t.mem base o 4=(4*wordsVal s.mem base a 4+p-wordsVal s.mem base b 4)%p := by
  unfold reference
  simp only [List.append_assoc]
  rw [WP.block_append_iff,loads_eq]
  refine WP.mono (loadsR_ok [.x1,.x2,.x3,.x4] hs.ptr ha ha8 (by decide) (by decide)) fun s1 ⟨e1,k1,_⟩ => ?_
  rw [WP.block_append_iff,loads_eq]
  refine WP.mono (loadsR_ok [.x9,.x10,.x11,.x12] (hs.of_keeps k1 (by decide)).ptr hb hb8 (by decide) (by decide)) fun s2 ⟨e2,k2,_⟩ => ?_
  have v1 : value (input s2)=wordsVal s.mem base a 4 := by
    rw [←input_value]
    calc
      regsVal s2 [.x1,.x2,.x3,.x4]=regsVal s1 [.x1,.x2,.x3,.x4] := by
        apply regsVal_congr
        intro r hr
        apply k2.gpr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide
      _ = _ := e1
  have v2 : value (other s2)=wordsVal s.mem base b 4 := by
    rw [←other_value]
    change regsVal s2 [.x9,.x10,.x11,.x12]=wordsVal s1.mem base b 4 at e2
    simpa only [k1.mem] using e2
  rw [WP.block_append_iff]
  refine WP.mono (prefix_ok s2) fun s3 ⟨e3,h3,z3,k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s3 z3) fun s4 ⟨e4,c4,k4⟩ => ?_
  rw [WP.block_append_iff]
  have z4 : s4.gpr .x17=0 := (k4.gpr .x17 (by decide)).trans z3
  refine WP.mono (back_ok s4 z4) fun s5 ⟨e5,k5⟩ => ?_
  have kk : Keeps (clob 4) s s5 := (k1.mono (by decide)).trans ((k2.mono (by decide)).trans
    ((k3.mono (by decide)).trans ((k4.mono (by decide)).trans (k5.mono (by decide)))))
  refine WP.mono (stores_ok [.x14,.x1,.x2,.x3] (hs.of_keeps kk (by decide)) ho ho8 (by decide)) fun t ⟨et,kt,ot⟩ => ?_
  change wordsVal t.mem base o 4=regsVal s5 [.x14,.x1,.x2,.x3] at et
  change VG.Proof.Mont.Outside base o 32 s5.mem t.mem at ot
  refine ⟨(Keeps.regs kk).trans (kt.mono (by regions_sub)),by simpa only [kk.mem] using ot,?_⟩
  rw [et,output_value,e5,e4,c4,e3,h3]
  change value (result (input s2) (other s2))=_
  rw [result_value _ _ (by rw [v1]; exact haP) (by rw [v2]; exact hbP),v1,v2]
end VG.Proof.P256.Linear.FortyOne
