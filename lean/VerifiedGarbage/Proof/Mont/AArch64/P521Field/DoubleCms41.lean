module

-- separate module: The fused-coefficient word and normalization replay at DoubleCms41 (cms_one_eight_ok) costs 2.44s of proof versus 0.37s of imports; DoubleBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsSmallLoaded
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsTopMath
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsOnePair
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsLow
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsAndWords
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsHigh
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsPrefix
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsFold
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeFold
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamMemory
public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def cmsOneEightClob : List Reg := [.x0,.x1,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x15]
def cmsOneEight (b : Nat) : List Instr := cmsOneFirst b++
  (cmsOnePair 0 (b+16)++(cmsOnePair 1 (b+32)++cmsOnePair 2 (b+48)))

theorem cms_one_eight_ok {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+64≤size) (hb8 : b%8=0) (hz : s.gpr .x2=0) :
    WP isa (.block (cmsOneEight b)) s fun t =>
      regsVal t cmsLowOut+wordsVal s.mem p b 8+1=regsVal s cmsLowOut+2^512*(!t.c).toNat ∧
      t.gpr .x15=cmsAndWords (cmsMiddleRegs.map t.gpr) ∧ Keeps cmsOneEightClob s t := by
  rw [cmsOneEight,WP.block_append_iff]
  refine WP.mono (cms_one_first_loaded hp (by omega_arith) hb8 hz) fun u ⟨eu,ku⟩ => ?_
  have hpu := hp.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cms_one_pair_loaded 0 (by decide) hpu (by omega_arith) (by omega_arith)) fun v ⟨ev,mv,kv⟩ => ?_
  have hpv := hpu.of_keeps kv (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cms_one_pair_loaded 1 (by decide) hpv (by omega_arith) (by omega_arith)) fun w ⟨ew,mw,kw⟩ => ?_
  have hpw := hpv.of_keeps kw (by decide)
  refine WP.mono (cms_one_pair_loaded 2 (by decide) hpw (by omega_arith) (by omega_arith)) fun t ⟨et,mt,kt⟩ => ?_
  have keptV : Keeps [.x0,.x1,.x3,.x4,.x5,.x6,.x15] s v :=
    (ku.mono (by decide)).trans (kv.mono (by decide))
  have keptW : Keeps [.x0,.x1,.x3,.x4,.x5,.x6,.x7,.x8,.x15] s w :=
    (keptV.mono (by decide)).trans (kw.mono (by decide))
  have tailU : Keeps [.x0,.x1,.x5,.x6,.x7,.x8,.x9,.x10,.x15] u t :=
    (kv.mono (by decide)).trans ((kw.mono (by decide)).trans (kt.mono (by decide)))
  have tailV : Keeps [.x0,.x1,.x7,.x8,.x9,.x10,.x15] v t :=
    (kw.mono (by decide)).trans (kt.mono (by decide))
  have new0 : regsVal t [.x3,.x4]=regsVal u [.x3,.x4] := regsVal_congr fun r h =>
    tailU.gpr r ((by decide : ∀r∈[Reg.x3,.x4],r∉[Reg.x0,.x1,.x5,.x6,.x7,.x8,.x9,.x10,.x15]) r h)
  have new1 : regsVal t [.x5,.x6]=regsVal v [.x5,.x6] := regsVal_congr fun r h =>
    tailV.gpr r ((by decide : ∀r∈[Reg.x5,.x6],r∉[Reg.x0,.x1,.x7,.x8,.x9,.x10,.x15]) r h)
  have new2 : regsVal t [.x7,.x8]=regsVal w [.x7,.x8] := regsVal_congr fun r h =>
    kt.gpr r ((by decide : ∀r∈[Reg.x7,.x8],r∉cmsOneLoadedClob 2) r h)
  have old1 : regsVal u [.x5,.x6]=regsVal s [.x5,.x6] := regsVal_congr fun r h =>
    ku.gpr r ((by decide : ∀r∈[Reg.x5,.x6],r∉[Reg.x0,.x1,.x3,.x4]) r h)
  have old2 : regsVal v [.x7,.x8]=regsVal s [.x7,.x8] := regsVal_congr fun r h =>
    keptV.gpr r ((by decide : ∀r∈[Reg.x7,.x8],r∉[Reg.x0,.x1,.x3,.x4,.x5,.x6,.x15]) r h)
  have old3 : regsVal w [.x9,.x10]=regsVal s [.x9,.x10] := regsVal_congr fun r h =>
    keptW.gpr r ((by decide : ∀r∈[Reg.x9,.x10],r∉[Reg.x0,.x1,.x3,.x4,.x5,.x6,.x7,.x8,.x15]) r h)
  simp only [cmsOneR0,cmsOneR1,cmsOnePrev] at ev ew et mv mw mt
  rw [←new0] at eu
  rw [←new1,old1,ku.mem] at ev
  rw [←new2,old2,keptV.mem] at ew
  rw [old3,keptW.mem] at et
  refine ⟨?_,?_,(ku.mono (by decide)).trans ((kv.mono (by decide)).trans
    ((kw.mono (by decide)).trans (kt.mono (by decide))))⟩
  · simp only [cmsLowOut,regsVal,wordsVal,Nat.mul_zero,Nat.add_zero,Nat.add_assoc,Nat.reduceAdd,Nat.mul_add] at eu ev ew et ⊢
    omega_using [eu,ev,ew,et]
  · rw [mw,mv] at mt
    rw [←tailU.gpr .x4 (by decide),←tailV.gpr .x5 (by decide),←tailV.gpr .x6 (by decide),
      ←kt.gpr .x7 (by decide),←kt.gpr .x8 (by decide)] at mt
    rw [mt]
    simp only [cmsMiddleRegs,List.map_cons,List.map_nil,cmsAndWords,BitVec.and_allOnes,BitVec.and_assoc]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value addWords)

def cmsFold41Clob : List Reg := [.x1,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12]

def cmsFold41Code : List Instr := [
  .lsr .x .x12 .x11 9,
  .subImm .x .x1 .x2 512,
  .logic .orr .x .x11 .x11 .x1,
  .subs .x .x1 .x1 .x1,
  .adcs .x .x1 .x3 .x12,
  .adcs .x .x1 .x15 .x2,
  .adcs .x .x1 .x11 .x2,
  .adcs .x .x3 .x3 .x12,
  .adcs .x .x4 .x4 .x2,
  .adcs .x .x5 .x5 .x2,
  .adcs .x .x6 .x6 .x2,
  .adcs .x .x7 .x7 .x2,
  .adcs .x .x8 .x8 .x2,
  .adcs .x .x9 .x9 .x2,
  .adcs .x .x10 .x10 .x2,
  .adc .x .x11 .x11 .x2,
  .movz .x .x1 511 0,
  .logic .and .x .x11 .x11 .x1]

theorem cms_fold41_words (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block cmsFold41Code) s fun t =>
      cmsScalarRegs.map t.gpr=cmsFoldResult s ∧ t.gpr .x1=511 ∧ Keeps cmsFold41Clob s t := by
  apply WP.of_runBlock
  simp only [cmsFold41Code,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.mul_zero,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hz,self_sub_carry,
    show BitVec.setWidth 64 (511 : BitVec 16) <<< 0=(511 : BitVec 64) from rfl,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · simp only [cmsScalarRegs,cmsFoldResult,cmsFoldSum,cmsFoldExtended,cmsFoldAddend,cmsFoldDetect,cmsFoldTop,cmsFoldHigh,
      cmsLowOut,List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.replicate_succ,List.replicate_zero,
      addWords,addCarry,carryOut,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
      List.take,List.getD,List.getElem?_cons,Size.bits]
    rfl
  · dsimp only [cmsFold41Clob]
    reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

theorem cms_fold41_ok (s : State) (hz : s.gpr .x2=0)
    (hand : s.gpr .x15=cmsAndWords (cmsMiddleRegs.map s.gpr))
    (hn : regsVal s cmsScalarRegs<33*(2^521-1)) :
    WP isa (.block cmsFold41Code) s fun t =>
      regsVal t cmsScalarRegs=regsVal s cmsScalarRegs%(2^521-1) ∧
      regsVal t cmsScalarRegs<2^521-1 ∧ t.gpr .x1=511 ∧ t.gpr .x2=0 ∧ Keeps cmsFold41Clob s t := by
  refine WP.mono (cms_fold41_words s hz) fun t ⟨words,m,k⟩ => ?_
  have hv := congrArg value words
  rw [value_map_gpr] at hv
  have hc := cms_fold_result_canonical s hand hn
  exact ⟨hv.trans hc.1,hv ▸ hc.2,m,(k.gpr .x2 (by decide)).trans hz,k⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

theorem cms_one_top_math (a x : Word) (c : Bool) (ha : a.toNat<16384) (hx : x.toNat<512) :
    (addCarry a (x^^^511) c).toNat=a.toNat+(511-x.toNat)+c.toNat := by
  have hm := cms_top_complement x hx
  have hc : carryOut a (x^^^511) c=false := by
    simp only [carryOut,hm,decide_eq_false_iff_not]
    have h := Bool.toNat_le c
    omega_arith
  have he := addCarry_value a (x^^^511) c
  rw [hm,hc] at he
  simpa only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] using he

def cmsOneTopCode : List Instr := [
  .movz .x .x1 511 0,
  .logic .eor .x .x0 .x0 .x1,
  .adc .x .x11 .x11 .x0]

theorem cms_one_top_ok (s : State) (ha : (s.gpr .x11).toNat<16384) (hx : (s.gpr .x0).toNat<512) :
    WP isa (.block cmsOneTopCode) s fun t =>
      (t.gpr .x11).toNat=(s.gpr .x11).toNat+(511-(s.gpr .x0).toNat)+s.c.toNat ∧
      t.gpr .x1=511 ∧ Keeps [.x0,.x1,.x11] s t := by
  apply WP.of_runBlock
  simp only [cmsOneTopCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.mul_zero,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.c_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    show BitVec.setWidth 64 (511 : BitVec 16) <<< 0=(511 : BitVec 64) from rfl,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · exact cms_one_top_math _ _ _ ha hx
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

def cmsOneAllClob : List Reg := [.x0,.x1,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x15]
def cmsOneAllCode (b : Nat) : List Instr := cmsOneEight b++
  (([.ldr .x .x0 .x28 (b+64)] : List Instr)++cmsOneTopCode)

theorem cms_one_all_ok {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+72≤size) (hb8 : b%8=0) (hz : s.gpr .x2=0)
    (ha : (s.gpr .x11).toNat<16384) (hx : wordsVal s.mem p b 9<2^521) :
    WP isa (.block (cmsOneAllCode b)) s fun t =>
      regsVal t cmsScalarRegs+wordsVal s.mem p b 9=regsVal s cmsScalarRegs+(2^521-1) ∧
      t.gpr .x1=511 ∧ t.gpr .x15=cmsAndWords (cmsMiddleRegs.map t.gpr) ∧ Keeps cmsOneAllClob s t := by
  rw [cmsOneAllCode,WP.block_append_iff]
  refine WP.mono (cms_one_eight_ok hp (by omega_arith) hb8 hz) fun u ⟨eu,mu,ku⟩ => ?_
  have hpu := hp.of_keeps ku (by decide)
  have hone : wordsVal s.mem p (b+64) 1=(word s.mem p (b+64)).toNat := by
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  have split := wordsVal_split s.mem p b 8 1
  simp only [Nat.reduceAdd,Nat.reduceMul,hone] at split
  have topBound : (word s.mem p (b+64)).toNat<512 := by omega_using [split,hx]
  rw [WP.block_append_iff]
  refine WP.mono (ldR_ok hpu (d:=b+64) (by omega_arith) (by omega_arith) .x0) fun v ⟨av,kv,cv⟩ => ?_
  have v11 : v.gpr .x11=s.gpr .x11 := (kv.gpr .x11 (by decide)).trans (ku.gpr .x11 (by decide))
  have bound0 : (v.gpr .x0).toNat<512 := by rw [av,ku.mem]; exact topBound
  refine WP.mono (cms_one_top_ok v (by rw [v11]; exact ha) bound0) fun t ⟨et,mt,kt⟩ => ?_
  have tlow : regsVal t cmsLowOut=regsVal u cmsLowOut := regsVal_congr fun r h =>
    (kt.gpr r ((by decide : ∀r∈cmsLowOut,r∉[Reg.x0,.x1,.x11]) r h)).trans
      (kv.gpr r ((by decide : ∀r∈cmsLowOut,r∉[Reg.x0]) r h))
  have tmid : cmsMiddleRegs.map t.gpr=cmsMiddleRegs.map u.gpr := List.map_congr_left fun r h =>
    (kt.gpr r ((by decide : ∀r∈cmsMiddleRegs,r∉[Reg.x0,.x1,.x11]) r h)).trans
      (kv.gpr r ((by decide : ∀r∈cmsMiddleRegs,r∉[Reg.x0]) r h))
  have tm : t.gpr .x15=u.gpr .x15 := (kt.gpr .x15 (by decide)).trans (kv.gpr .x15 (by decide))
  have splitRegs (w : State) : regsVal w cmsScalarRegs=regsVal w cmsLowOut+2^512*(w.gpr .x11).toNat := by
    have hs : cmsScalarRegs=cmsLowOut++[.x11] := rfl
    rw [hs,regsVal_append]
    simp only [show cmsLowOut.length=8 from by decide,Nat.reduceMul,regsVal,Nat.mul_zero,Nat.add_zero]
  rw [v11,av,ku.mem,cv] at et
  have hc : (!u.c).toNat+u.c.toNat=1 := by cases u.c <;> rfl
  refine ⟨?_,mt,by rw [tm,tmid]; exact mu,
    (ku.mono (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide)))⟩
  rw [splitRegs,splitRegs,tlow]
  omega_using [eu,et,hc,split,topBound]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (storesR)
open VG.Proof.Ed25519.AArch64

def cms41Clob : List Reg := [.x0,.x1,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15]
def cms41Code (a b o : Nat) : List Instr := cmsSmallLoaded false a++
  (cmsOneAllCode b++(cmsFold41Code++storesR .x26 cmsScalarRegs o))

theorem cms41_ok {s : State} {p po : Addr} {size room a b o : Nat}
    (hp : Ptr s .x28 p size) (ho : PtrW s .x26 po room)
    (hA : a+72≤size) (hB : b+72≤size) (hO : o+72≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0) (hz : s.gpr .x2=0)
    (ha : wordsVal s.mem p a 9<2*(2^521-1)) (hb : wordsVal s.mem p b 9<2^521-1) :
    WP isa (.block (cms41Code a b o)) s fun t =>
      wordsVal t.mem po o 9=(4*wordsVal s.mem p a 9+((2^521-1)-wordsVal s.mem p b 9))%(2^521-1) ∧
      wordsVal t.mem po o 9<2^521-1 ∧ t.gpr .x1=511 ∧ t.gpr .x2=0 ∧
      KeepRegs cms41Clob s t ∧ Outside po o 72 s.mem t.mem := by
  rw [cms41Code,WP.block_append_iff]
  refine WP.mono (cms_small_loaded_value false hp hA ha8 ha) fun u ⟨eu,ku⟩ => ?_
  simp only [Bool.false_eq_true,ite_false] at eu
  have hpu := hp.of_keeps ku (by decide)
  have uz : u.gpr .x2=0 := (ku.gpr .x2 (by decide)).trans hz
  have top : (u.gpr .x11).toNat<16384 := by
    have hs := cms_scalar_split u
    omega_using [hs,eu,ha]
  have ub : wordsVal u.mem p b 9<2^521 := by rw [ku.mem]; omega_using [hb]
  rw [WP.block_append_iff]
  refine WP.mono (cms_one_all_ok hpu hB hb8 uz top ub) fun v ⟨ev,_,mid,kv⟩ => ?_
  rw [ku.mem,eu] at ev
  have vn : regsVal v cmsScalarRegs=4*wordsVal s.mem p a 9+((2^521-1)-wordsVal s.mem p b 9) := by
    omega_using [ev,hb]
  have bound : regsVal v cmsScalarRegs<33*(2^521-1) := by omega_using [ev,ha]
  have vz : v.gpr .x2=0 := (kv.gpr .x2 (by decide)).trans uz
  rw [WP.block_append_iff]
  refine WP.mono (cms_fold41_ok v vz mid bound) fun w ⟨vw,bw,mw,zw,kw⟩ => ?_
  rw [vn] at vw
  have kept : Keeps cms41Clob s w := (ku.mono (by decide)).trans ((kv.mono (by decide)).trans (kw.mono (by decide)))
  have how := ho.of_keepRegs (Keeps.regs kept) (by decide)
  refine WP.mono (storesR_ok cmsScalarRegs how (by simpa only [show cmsScalarRegs.length=9 from by decide] using hO)
    ho8 (by decide)) fun t ⟨stored,kt,ot⟩ => ?_
  simp only [show cmsScalarRegs.length=9 from by decide] at stored ot
  exact ⟨stored.trans vw,stored ▸ bw,(kt.gpr .x1 (by simp)).trans mw,(kt.gpr .x2 (by simp)).trans zw,
    (Keeps.regs kept).trans (kt.mono (by simp)),by rw [kept.mem] at ot; exact ot⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field

def doubleCms41Code : List Instr := ((doubleFnBlocks.drop 87).flatten.drop 30).take 73
def doubleCms41Early : List Instr := doubleCms41Code.take 18
def doubleCms41Tail : List Instr := ((doubleFnBlocks.drop 88).flatten.drop 16).take 55

theorem doubleCms41_source : doubleCms41Code=(doubleFnBlocks.flatten.drop 2814).take 73 := by
  have h := drop_flatten_prefix doubleFnBlocks 87 2784 30
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 73) h.symm

theorem doubleCms41_hoist : hoistLoads .x28 doubleCms41Early=some (loadsR .x28 cmsSmallInputs 216,cmsFourCode) := by lit_decide

theorem doubleCms41_run (s : State) : runBlock isa doubleCms41Code s=runBlock isa (cms41Code 216 432 0) s := by
  have hs : doubleCms41Code=doubleCms41Early++doubleCms41Tail := by decide
  have hn : cms41Code 216 432 0=(loadsR .x28 cmsSmallInputs 216++cmsFourCode)++doubleCms41Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistLoads_run doubleCms41_hoist) (fun _ => rfl) s

theorem double_cms41_ok {s : State} {p po : Addr} {size room : Nat}
    (hp : Ptr s .x28 p size) (ho : PtrW s .x26 po room)
    (hA : 288≤size) (hB : 504≤size) (hO : 72≤room) (hz : s.gpr .x2=0)
    (ha : wordsVal s.mem p 216 9<2*(2^521-1)) (hb : wordsVal s.mem p 432 9<2^521-1) :
    WP isa (.block doubleCms41Code) s fun t =>
      wordsVal t.mem po 0 9=(4*wordsVal s.mem p 216 9+((2^521-1)-wordsVal s.mem p 432 9))%(2^521-1) ∧
      wordsVal t.mem po 0 9<2^521-1 ∧ t.gpr .x1=511 ∧ t.gpr .x2=0 ∧
      KeepRegs cms41Clob s t ∧ Outside po 0 72 s.mem t.mem := by
  have h := cms41_ok (a:=216) (b:=432) (o:=0) hp ho hA hB hO (by decide) (by decide) (by decide) hz ha hb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(doubleCms41_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field
