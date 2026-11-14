module

-- separate module: The fused-coefficient word and normalization replay at DoubleCms38 (cms_fold38_words) costs 1.60s of proof versus 0.36s of imports; DoubleBlocks composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsSmallLoaded
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsEightEight
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsTopMath
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsPrefix
import VerifiedGarbage.Proof.Framework.Block
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
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value addWords)

def cmsFold38Clob : List Reg := [.x0,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12]

def cmsFold38Code : List Instr := [
  .lsr .x .x12 .x11 9,
  .subImm .x .x0 .x2 512,
  .logic .orr .x .x11 .x11 .x0,
  .subs .x .x0 .x0 .x0,
  .adcs .x .x0 .x3 .x12,
  .adcs .x .x0 .x15 .x2,
  .adcs .x .x0 .x11 .x2,
  .adcs .x .x3 .x3 .x12,
  .adcs .x .x4 .x4 .x2,
  .adcs .x .x5 .x5 .x2,
  .adcs .x .x6 .x6 .x2,
  .adcs .x .x7 .x7 .x2,
  .adcs .x .x8 .x8 .x2,
  .adcs .x .x9 .x9 .x2,
  .adcs .x .x10 .x10 .x2,
  .adc .x .x11 .x11 .x2,
  .logic .and .x .x11 .x11 .x1]

theorem cms_fold38_words (s : State) (hz : s.gpr .x2=0) (hm : s.gpr .x1=511) :
    WP isa (.block cmsFold38Code) s fun t =>
      cmsScalarRegs.map t.gpr=cmsFoldResult s ∧ t.gpr .x1=511 ∧ Keeps cmsFold38Clob s t := by
  apply WP.of_runBlock
  simp only [cmsFold38Code,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hz,hm,self_sub_carry,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · simp only [cmsScalarRegs,cmsFoldResult,cmsFoldSum,cmsFoldExtended,cmsFoldAddend,cmsFoldDetect,cmsFoldTop,cmsFoldHigh,
      cmsLowOut,List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.replicate_succ,List.replicate_zero,
      addWords,addCarry,carryOut,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
      List.take,List.getD,List.getElem?_cons,Size.bits]
    rfl
  · dsimp only [cmsFold38Clob]
    reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

theorem cms_fold38_ok (s : State) (hz : s.gpr .x2=0) (hm : s.gpr .x1=511)
    (hand : s.gpr .x15=cmsAndWords (cmsMiddleRegs.map s.gpr))
    (hn : regsVal s cmsScalarRegs<33*(2^521-1)) :
    WP isa (.block cmsFold38Code) s fun t =>
      regsVal t cmsScalarRegs=regsVal s cmsScalarRegs%(2^521-1) ∧
      regsVal t cmsScalarRegs<2^521-1 ∧ t.gpr .x1=511 ∧ t.gpr .x2=0 ∧ Keeps cmsFold38Clob s t := by
  refine WP.mono (cms_fold38_words s hz hm) fun t ⟨words,m,k⟩ => ?_
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

theorem cms_eight_top_math (a x prev : Word) (c : Bool) (ha : a.toNat<16384) (hx : x.toNat<512) :
    (addCarry a (cmsEightShift (x^^^511) prev) c).toNat=
      a.toNat+8*(511-x.toNat)+(mulHi 8 prev).toNat+c.toNat := by
  have hm := cms_top_complement x hx
  have hh : (mulHi 8 prev).toNat<8 := by
    have he := mul_lo_hi (8 : Word) prev
    have hp := prev.isLt
    simp only [show (8 : Word).toNat=8 from rfl] at he
    omega_arith
  have hl : (8*(x^^^511)).toNat=8*(511-x.toNat) := by
    rw [BitVec.toNat_mul,hm]
    simp only [show (8 : Word).toNat=8 from rfl]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have hs := cms_eight_shift_value (x^^^511) prev
  rw [hl] at hs
  have hc : carryOut a (cmsEightShift (x^^^511) prev) c=false := by
    simp only [carryOut,hs,decide_eq_false_iff_not]
    have h := Bool.toNat_le c
    omega_arith
  have he := addCarry_value a (cmsEightShift (x^^^511) prev) c
  rw [hc,hs] at he
  simpa only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using he

def cmsEightTopCode : List Instr := [
  .logic .eor .x .x0 .x0 .x1,
  .extr .x .x0 .x0 .x23 61,
  .adc .x .x11 .x11 .x0]

theorem cms_eight_top_ok (s : State) (ha : (s.gpr .x11).toNat<16384) (hx : (s.gpr .x0).toNat<512)
    (hm : s.gpr .x1=511) :
    WP isa (.block cmsEightTopCode) s fun t =>
      (t.gpr .x11).toNat=(s.gpr .x11).toNat+8*(511-(s.gpr .x0).toNat)+
        (mulHi 8 (s.gpr .x23)).toNat+s.c.toNat ∧ Keeps [.x0,.x11] s t := by
  have extr (n m : Word) : (n++m).extractLsb' 61 64=cmsEightShift n m := cms_shift_extract n m 3 (by decide)
  apply WP.of_runBlock
  simp only [cmsEightTopCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.c_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hm,extr,
    Option.some.injEq,exists_eq_left']
  refine ⟨cms_eight_top_math _ _ _ _ ha hx,⟨?_,?_,?_,?_,?_⟩⟩
  · reg_keeps
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def cmsEightAllClob : List Reg := [.x0,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x15,.x20,.x21,.x22,.x23]
def cmsEightAllCode (b : Nat) : List Instr := cmsEightEight b++
  (([.ldr .x .x0 .x28 (b+64)] : List Instr)++cmsEightTopCode)

theorem cms_eight_all_ok {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+72≤size) (hb8 : b%8=0) (hz : s.gpr .x2=0) (hm : s.gpr .x1=511)
    (ha : (s.gpr .x11).toNat<16384) (hx : wordsVal s.mem p b 9<2^521) :
    WP isa (.block (cmsEightAllCode b)) s fun t =>
      regsVal t cmsScalarRegs+8*wordsVal s.mem p b 9=regsVal s cmsScalarRegs+8*(2^521-1) ∧
      t.gpr .x1=511 ∧ t.gpr .x15=cmsAndWords (cmsMiddleRegs.map t.gpr) ∧ Keeps cmsEightAllClob s t := by
  rw [cmsEightAllCode,WP.block_append_iff]
  refine WP.mono (cms_eight_eight_ok hp (by omega_arith) hb8 hz) fun u ⟨eu,_,mu,ku⟩ => ?_
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
  refine WP.mono (cms_eight_top_ok v (by rw [v11]; exact ha) bound0 ((kv.gpr .x1 (by decide)).trans ((ku.gpr .x1 (by decide)).trans hm))) fun t ⟨et,kt⟩ => ?_
  have tlow : regsVal t cmsLowOut=regsVal u cmsLowOut := regsVal_congr fun r h =>
    (kt.gpr r ((by decide : ∀r∈cmsLowOut,r∉[Reg.x0,.x11]) r h)).trans
      (kv.gpr r ((by decide : ∀r∈cmsLowOut,r∉[Reg.x0]) r h))
  have tmid : cmsMiddleRegs.map t.gpr=cmsMiddleRegs.map u.gpr := List.map_congr_left fun r h =>
    (kt.gpr r ((by decide : ∀r∈cmsMiddleRegs,r∉[Reg.x0,.x11]) r h)).trans
      (kv.gpr r ((by decide : ∀r∈cmsMiddleRegs,r∉[Reg.x0]) r h))
  have tm : t.gpr .x15=u.gpr .x15 := (kt.gpr .x15 (by decide)).trans (kv.gpr .x15 (by decide))
  have splitRegs (w : State) : regsVal w cmsScalarRegs=regsVal w cmsLowOut+2^512*(w.gpr .x11).toNat := by
    have hs : cmsScalarRegs=cmsLowOut++[.x11] := rfl
    rw [hs,regsVal_append]
    simp only [show cmsLowOut.length=8 from by decide,Nat.reduceMul,regsVal,Nat.mul_zero,Nat.add_zero]
  rw [v11,av,ku.mem,cv,kv.gpr .x23 (by decide)] at et
  refine ⟨?_,(kt.gpr .x1 (by decide)).trans ((kv.gpr .x1 (by decide)).trans ((ku.gpr .x1 (by decide)).trans hm)),by rw [tm,tmid]; exact mu,
    (ku.mono (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide)))⟩
  rw [splitRegs,splitRegs,tlow]
  omega_using [eu,et,split,topBound]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (storesR)
open VG.Proof.Ed25519.AArch64

def cms38Clob : List Reg := [.x0,.x1,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x20,.x21,.x22,.x23]
def cms38Code (a b o : Nat) : List Instr := cmsSmallLoaded true a++
  (cmsEightAllCode b++(cmsFold38Code++storesR .x26 cmsScalarRegs o))

theorem cms38_ok {s : State} {p po : Addr} {size room a b o : Nat}
    (hp : Ptr s .x28 p size) (ho : PtrW s .x26 po room)
    (hA : a+72≤size) (hB : b+72≤size) (hO : o+72≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0) (hz : s.gpr .x2=0) (hm : s.gpr .x1=511)
    (ha : wordsVal s.mem p a 9<2*(2^521-1)) (hb : wordsVal s.mem p b 9<2^521-1) :
    WP isa (.block (cms38Code a b o)) s fun t =>
      wordsVal t.mem po o 9=(3*wordsVal s.mem p a 9+8*((2^521-1)-wordsVal s.mem p b 9))%(2^521-1) ∧
      wordsVal t.mem po o 9<2^521-1 ∧ t.gpr .x1=511 ∧ t.gpr .x2=0 ∧
      KeepRegs cms38Clob s t ∧ Outside po o 72 s.mem t.mem := by
  rw [cms38Code,WP.block_append_iff]
  refine WP.mono (cms_small_loaded_value true hp hA ha8 ha) fun u ⟨eu,ku⟩ => ?_
  simp only [ite_true] at eu
  have hpu := hp.of_keeps ku (by decide)
  have uz : u.gpr .x2=0 := (ku.gpr .x2 (by decide)).trans hz
  have um : u.gpr .x1=511 := (ku.gpr .x1 (by decide)).trans hm
  have top : (u.gpr .x11).toNat<16384 := by
    have hs := cms_scalar_split u
    omega_using [hs,eu,ha]
  have ub : wordsVal u.mem p b 9<2^521 := by rw [ku.mem]; omega_using [hb]
  rw [WP.block_append_iff]
  refine WP.mono (cms_eight_all_ok hpu hB hb8 uz um top ub) fun v ⟨ev,vm,mid,kv⟩ => ?_
  rw [ku.mem,eu] at ev
  have vn : regsVal v cmsScalarRegs=3*wordsVal s.mem p a 9+8*((2^521-1)-wordsVal s.mem p b 9) := by
    omega_using [ev,hb]
  have bound : regsVal v cmsScalarRegs<33*(2^521-1) := by omega_using [ev,ha]
  have vz : v.gpr .x2=0 := (kv.gpr .x2 (by decide)).trans uz
  rw [WP.block_append_iff]
  refine WP.mono (cms_fold38_ok v vz vm mid bound) fun w ⟨vw,bw,mw,zw,kw⟩ => ?_
  rw [vn] at vw
  have kept : Keeps cms38Clob s w := (ku.mono (by decide)).trans ((kv.mono (by decide)).trans (kw.mono (by decide)))
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

def doubleCms38Code : List Instr := ((doubleFnBlocks.drop 90).flatten.drop 7).take 103
def doubleCms38Early : List Instr := doubleCms38Code.take 27
def doubleCms38Tail : List Instr := ((doubleFnBlocks.drop 91).flatten.drop 2).take 76

theorem doubleCms38_source : doubleCms38Code=(doubleFnBlocks.flatten.drop 2887).take 103 := by
  have h := drop_flatten_prefix doubleFnBlocks 90 2880 7
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 103) h.symm

theorem doubleCms38_hoist : hoistLoads .x28 doubleCms38Early=some (loadsR .x28 cmsSmallInputs 360,cmsThreeCode) := by lit_decide

theorem doubleCms38_run (s : State) : runBlock isa doubleCms38Code s=runBlock isa (cms38Code 360 288 72) s := by
  have hs : doubleCms38Code=doubleCms38Early++doubleCms38Tail := by decide
  have hn : cms38Code 360 288 72=(loadsR .x28 cmsSmallInputs 360++cmsThreeCode)++doubleCms38Tail := by decide
  rw [hs,hn]
  exact append_run_eq (hoistLoads_run doubleCms38_hoist) (fun _ => rfl) s

theorem double_cms38_ok {s : State} {p po : Addr} {size room : Nat}
    (hp : Ptr s .x28 p size) (ho : PtrW s .x26 po room)
    (hA : 432≤size) (hB : 360≤size) (hO : 144≤room) (hz : s.gpr .x2=0) (hm : s.gpr .x1=511)
    (ha : wordsVal s.mem p 360 9<2*(2^521-1)) (hb : wordsVal s.mem p 288 9<2^521-1) :
    WP isa (.block doubleCms38Code) s fun t =>
      wordsVal t.mem po 72 9=(3*wordsVal s.mem p 360 9+8*((2^521-1)-wordsVal s.mem p 288 9))%(2^521-1) ∧
      wordsVal t.mem po 72 9<2^521-1 ∧ t.gpr .x1=511 ∧ t.gpr .x2=0 ∧
      KeepRegs cms38Clob s t ∧ Outside po 72 72 s.mem t.mem := by
  have h := cms38_ok (a:=360) (b:=288) (o:=72) hp ho hA hB hO (by decide) (by decide) (by decide) hz hm ha hb
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP h
  exact WP.of_runBlock ⟨t,(doubleCms38_run s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field
