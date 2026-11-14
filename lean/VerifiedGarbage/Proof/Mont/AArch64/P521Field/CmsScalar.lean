module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsPrefix
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsPairValue
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearPair
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def cmsFirst : List Instr := [
  .movz .x .x1 12 0,
  .mul .x .x3 .x1 .x6,
  .mul .x .x4 .x1 .x7,
  .umulh .x6 .x1 .x6,
  .adds .x .x4 .x4 .x6,
  .umulh .x7 .x1 .x7]

def cmsFirstClob : List Reg := [.x1,.x3,.x4,.x6,.x7]

theorem cms_first_ok (s : State) :
    WP isa (.block cmsFirst) s fun t =>
      t.gpr .x3=12*s.gpr .x6 ∧
      t.gpr .x4=addCarry (12*s.gpr .x7) (mulHi 12 (s.gpr .x6)) false ∧
      t.gpr .x7=mulHi 12 (s.gpr .x7) ∧
      t.c=carryOut (12*s.gpr .x7) (mulHi 12 (s.gpr .x6)) false ∧
      t.gpr .x1=12 ∧ Keeps cmsFirstClob s t := by
  apply WP.of_runBlock
  simp only [cmsFirst,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.mul_zero,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_write,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    show BitVec.setWidth 64 (12 : BitVec 16) <<< 0=(12 : BitVec 64) from rfl,
    Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,by rfl,True.intro,by rfl,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · dsimp only [cmsFirstClob]
    reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

theorem cms_first_value (s : State) :
    WP isa (.block cmsFirst) s fun t =>
      regsVal t [.x3,.x4]+2^128*((t.gpr .x7).toNat+t.c.toNat)=12*regsVal s [.x6,.x7] ∧
      t.gpr .x1=12 ∧ Keeps cmsFirstClob s t := by
  refine WP.mono (cms_first_ok s) fun t ⟨a0,a1,hh,cc,k1,k⟩ => ?_
  refine ⟨?_,k1,k⟩
  simp only [regsVal,Nat.mul_zero,Nat.add_zero,a0,a1,hh,cc,Nat.mul_add]
  have m0 := mul_lo_hi 12 (s.gpr .x6)
  have m1 := mul_lo_hi 12 (s.gpr .x7)
  have ev := addCarry_value (12*s.gpr .x7) (mulHi 12 (s.gpr .x6)) false
  simp only [show (12 : BitVec 64).toNat=12 from rfl,Bool.toNat_false,Nat.add_zero] at m0 m1 ev
  omega_using [m0,m1,ev]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def cmsLoadedFirst (b : Nat) : List Instr := twoLoads .x28 .x6 .x7 b++cmsFirst

theorem cms_loaded_first_value {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+16≤size) (hb8 : b%8=0) :
    WP isa (.block (cmsLoadedFirst b)) s fun t =>
      regsVal t [.x3,.x4]+2^128*((t.gpr .x7).toNat+t.c.toNat)=12*wordsVal s.mem p b 2 ∧
      t.gpr .x1=12 ∧ Keeps cmsFirstClob s t := by
  rw [cmsLoadedFirst,WP.block_append_iff]
  refine WP.mono (two_loads_ok hp hb hb8 (by decide) (by decide)) fun u ⟨b0,b1,_,ku⟩ => ?_
  refine WP.mono (cms_first_value u) fun t ⟨ev,k1,kt⟩ => ?_
  simp only [regsVal,Nat.mul_zero,Nat.add_zero,b0,b1] at ev
  exact ⟨by simpa only [regsVal,wordsVal,Nat.mul_zero,Nat.add_zero] using ev,k1,
    (ku.mono (by decide)).trans kt⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def cmsScalarClob : List Reg := [.x1,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14]

def cmsScalarEight (b : Nat) : List Instr := cmsLoadedFirst b++
  (cmsLoadedPair 0 (b+16)++(cmsLoadedPair 1 (b+32)++cmsLoadedPair 2 (b+48)))

theorem cms_scalar_eight_ok {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+64≤size) (hb8 : b%8=0) :
    WP isa (.block (cmsScalarEight b)) s fun t =>
      cmsScalarInv t p b 8 ∧ t.gpr .x1=12 ∧ Keeps cmsScalarClob s t := by
  rw [cmsScalarEight,WP.block_append_iff]
  refine WP.mono (cms_loaded_first_value hp (by omega_arith) hb8) fun u ⟨eu,ku1,ku⟩ => ?_
  have hpU := hp.of_keeps ku (by decide)
  have hu : cmsScalarInv u p b 2 := by
    change regsVal u [.x3,.x4]+2^128*((u.gpr .x7).toNat+u.c.toNat)=12*wordsVal u.mem p b 2
    rw [ku.mem]
    exact eu
  rw [WP.block_append_iff]
  refine WP.mono (cms_prefix_step 0 (by decide) hpU (by omega_arith) hb8 ku1 hu) fun v ⟨ev,kv1,kv⟩ => ?_
  have hpV := hpU.of_keeps kv (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cms_prefix_step 1 (by decide) hpV (by omega_arith) hb8 kv1 ev) fun w ⟨ew,kw1,kw⟩ => ?_
  have hpW := hpV.of_keeps kw (by decide)
  refine WP.mono (cms_prefix_step 2 (by decide) hpW (by omega_arith) hb8 kw1 ew) fun t ⟨et,kt1,kt⟩ => ?_
  exact ⟨et,kt1,(ku.mono (by decide)).trans ((kv.mono (by decide)).trans
    ((kw.mono (by decide)).trans (kt.mono (by decide))))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

theorem cms_top_math (a h : Word) (c : Bool) (ha : a.toNat<1024) (hh : h.toNat+c.toNat<12) :
    (addCarry (12*a) h c).toNat=12*a.toNat+h.toNat+c.toNat := by
  have hm : ((12 : Word)*a).toNat=12*a.toNat := by
    rw [BitVec.toNat_mul,show (12 : Word).toNat=12 from rfl]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have hc : carryOut (12*a) h c=false := by
    simp only [carryOut,hm,decide_eq_false_iff_not]
    omega_arith
  have he := addCarry_value (12*a) h c
  rw [hm,hc] at he
  simpa only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero] using he

def cmsScalarTop : List Instr := [.mul .x .x11 .x1 .x14,.adc .x .x11 .x11 .x13]

theorem cms_scalar_top_ok (s : State) (hk : s.gpr .x1=12)
    (ha : (s.gpr .x14).toNat<1024) (hh : (s.gpr .x13).toNat+s.c.toNat<12) :
    WP isa (.block cmsScalarTop) s fun t =>
      (t.gpr .x11).toNat=12*(s.gpr .x14).toNat+(s.gpr .x13).toNat+s.c.toNat ∧ Keeps [.x11] s t := by
  apply WP.of_runBlock
  simp only [cmsScalarTop,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,RegUpd.c_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hk,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,?_,?_,?_,?_⟩⟩
  · exact cms_top_math _ _ _ ha hh
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]
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

def cmsScalarCode (b : Nat) : List Instr := cmsScalarEight b++
  (([.ldr .x .x14 .x28 (b+64)] : List Instr)++cmsScalarTop)

theorem cms_scalar_ok {s : State} {p : Addr} {size b : Nat}
    (hp : Ptr s .x28 p size) (hb : b+72≤size) (hb8 : b%8=0)
    (ha : wordsVal s.mem p b 9<2*(2^521-1)) :
    WP isa (.block (cmsScalarCode b)) s fun t =>
      regsVal t cmsScalarRegs=12*wordsVal s.mem p b 9 ∧ t.gpr .x1=12 ∧ Keeps cmsScalarClob s t := by
  rw [cmsScalarCode,WP.block_append_iff]
  refine WP.mono (cms_scalar_eight_ok hp (by omega_arith) hb8) fun u ⟨eu,ku1,ku⟩ => ?_
  have hpu := hp.of_keeps ku (by decide)
  have hone : wordsVal s.mem p (b+64) 1=(word s.mem p (b+64)).toNat := by
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  have split := wordsVal_split s.mem p b 8 1
  simp only [Nat.reduceAdd,Nat.reduceMul,hone] at split
  have topBound : (word s.mem p (b+64)).toNat<1024 := by omega_using [split,ha]
  have hiBound : (u.gpr .x13).toNat+u.c.toNat<12 := by
    have hl := wordsVal_lt u.mem p b 8
    have ep := eu
    dsimp only [cmsScalarInv,cmsPrefixHigh] at ep
    simp only [Nat.reduceMul] at hl ep
    omega_using [hl,ep]
  rw [WP.block_append_iff]
  refine WP.mono (ldR_ok hpu (d:=b+64) (by omega_arith) (by omega_arith) .x14)
    fun v ⟨av,kv,cv⟩ => ?_
  have kv1 : v.gpr .x1=12 := (kv.gpr .x1 (by decide)).trans ku1
  have va : (v.gpr .x14).toNat<1024 := by rw [av,ku.mem]; exact topBound
  have vh : (v.gpr .x13).toNat+v.c.toNat<12 := by rw [kv.gpr .x13 (by decide),cv]; exact hiBound
  refine WP.mono (cms_scalar_top_ok v kv1 va vh) fun t ⟨vt,kt⟩ => ?_
  have low : regsVal t (cmsScalarRegs.take 8)=regsVal u (cmsScalarRegs.take 8) := regsVal_congr fun r h =>
    (kt.gpr r ((by decide : ∀r∈cmsScalarRegs.take 8,r∉[Reg.x11]) r h)).trans
      (kv.gpr r ((by decide : ∀r∈cmsScalarRegs.take 8,r∉[Reg.x14]) r h))
  have splitRegs : cmsScalarRegs=cmsScalarRegs.take 8++[.x11] := rfl
  have ep := eu
  dsimp only [cmsScalarInv,cmsPrefixHigh] at ep
  simp only [Nat.reduceMul,ku.mem] at ep
  rw [av,kv.gpr .x13 (by decide),cv,ku.mem] at vt
  refine ⟨?_,(kt.gpr .x1 (by decide)).trans kv1,
    ku.trans ((kv.mono (by decide)).trans (kt.mono (by decide)))⟩
  rw [splitRegs,regsVal_append]
  have hs : regsVal t [.x11]=(t.gpr .x11).toNat := by simp only [regsVal,Nat.mul_zero,Nat.add_zero]
  rw [hs,show (cmsScalarRegs.take 8).length=8 from by decide]
  simp only [Nat.reduceMul]
  rw [low,split]
  omega_using [ep,vt]

end VG.Proof.Mont.AArch64.P521Field
