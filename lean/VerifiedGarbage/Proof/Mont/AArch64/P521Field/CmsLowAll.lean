module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsLowLoaded
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulFirst
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsTopMath
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearMask
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsPrefix

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
