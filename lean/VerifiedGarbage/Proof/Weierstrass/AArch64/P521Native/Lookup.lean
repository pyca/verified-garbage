module

-- separate module: this consolidated proof replays 0.79s of elaboration/kernel work versus 0.28s importing its dependencies (local Lean trace); retaining the boundary avoids replaying it in its sole importer.

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.LookupCode
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.LookupEntry
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.OuterBlocks
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.LookupStoreVectors
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AddrArith

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (storesR)

theorem storesR_any_ok {size : Nat} {rn : Reg} : ∀(rs : List Reg) {s : State} {base : Addr} {o : Nat},
    PtrW s rn base size → o+8*rs.length≤size → o%8=0 →
    WP isa (.block (storesR rn rs o)) s fun t =>
      wordsVal t.mem base o rs.length=regsVal s rs ∧ KeepRegs [] s t ∧
      Outside base o (8*rs.length) s.mem t.mem
  | [],s,_,_,_,_,_ => WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | r::rs,s,base,o,hp,ho,ho8 => by
    have hn := hp.nowrap
    have he := hp.enc
    simp only [List.length_cons] at ho
    rw [storesR,←List.singleton_append,WP.block_append_iff]
    refine WP.mono (stR_ok hp (d:=o) (by omega_arith) ho8 r) fun u e => ?_
    have hpu : PtrW u rn base size := by subst e; exact ⟨hp.reg,hp.st,hp.enc,hp.nowrap⟩
    have ou : Outside base o 8 s.mem u.mem := by rw [e]; exact writeW_outside _ _ _ (by omega_arith)
    refine WP.mono (storesR_any_ok rs hpu (o:=o+8) (by omega_arith) (by omega_arith))
      fun t ⟨rest,k,frame⟩ => ?_
    have ku : KeepRegs [] s u := by subst e; exact ⟨fun _ _ => rfl,rfl,rfl,rfl⟩
    refine ⟨?_,ku.trans k,?_⟩
    · rw [List.length_cons,wordsVal,frame.word (by omega_arith) (by omega_arith),e,word_writeW_self,rest,
        regsVal,regsVal_congr (s:=s) (s':=u) (fun q _ => by rw [e])]
    · intro x hx
      simp only [List.length_cons] at hx
      rw [frame x (by omega_arith),ou x (by omega_arith)]

theorem storesR_novec (rn : Reg) : ∀(rs : List Reg) (d : Nat),∀i∈storesR rn rs d,vdstOf i=none
  | [],_,_,h => False.elim (List.not_mem_nil h)
  | r::rs,d,i,hi => by
    simp only [storesR,List.mem_cons] at hi
    rcases hi with rfl|h
    · rfl
    · exact storesR_novec rn rs (d+8) i h

theorem storesR_any_vectors {s : State} {base : Addr} {size o : Nat} {rn : Reg} (rs : List Reg)
    (hp : PtrW s rn base size) (ho : o+8*rs.length≤size) (ho8 : o%8=0) :
    WP isa (.block (storesR rn rs o)) s fun t =>
      wordsVal t.mem base o rs.length=regsVal s rs ∧ KeepRegs [] s t ∧
      Outside base o (8*rs.length) s.mem t.mem ∧ t.v=s.v := by
  exact WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (storesR_novec rn rs o)
    (storesR_any_ok rs hp ho ho8)) (fun _ ⟨⟨v,k,o⟩,vec⟩ => ⟨v,k,o,vec⟩)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Impl.Mont.AArch64 (storesR)
open VG.Impl.Weierstrass.AArch64.P521Native

def lookupZFlagCode : List Instr := [.movz .x .x4 1 0,.subs .x .x16 .x2 .x3,.cselc .x .x4 .x4 .x3 .ne]
def lookupZRegs : List Reg := [.x4,.x3,.x3,.x3,.x3,.x3,.x3,.x3,.x3]
def lookupZOutputCode : List Instr := lookupZFlagCode++storesR .x0 lookupZRegs 1648

theorem lookupZOutput_source : lookupZOutputCode=(outerBlock142.drop 628).take 12 := by lit_decide

theorem lookup_z_flag_ok (s : State) (zero : s.gpr .x3=0#64) :
    WP isa (.block lookupZFlagCode) s fun t =>
      t.gpr .x4=(if s.gpr .x2=0 then 0 else 1) ∧ Keeps [.x4,.x16] s t ∧ t.v=s.v := by
  have zf (u : State) (a : Word) : (u.addWithCarry .x .x16 a (~~~(0#64)) true).zf=decide (a=0#64) := by
    change decide (addCarry a (~~~(0#64)) true=0#64)=decide (a=0#64)
    have h : addCarry a (~~~(0#64)) true=a := by
      change a+~~~(0#64)+1#64=a
      rw [BitVec.add_assoc,show ~~~(0#64)+1#64=0#64 from rfl]
      exact BitVec.add_zero a
    rw [h]
  apply WP.of_runBlock
  simp only [lookupZFlagCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,CondCode.holds,BitVec.setWidth_eq,
    zero,zf,show BitVec.setWidth 64 (1 : BitVec 16)=1#64 from rfl,Size.bits,Nat.mul_zero,Nat.reduceLT,BitVec.shiftLeft_zero,reduceCtorEq,ite_true,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · change (if !(decide (s.gpr .x2=0#64)) then 1#64 else 0#64)=(if s.gpr .x2=0#64 then 0#64 else 1#64)
    by_cases h : s.gpr .x2=0#64 <;> simp [h]
  · reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]
  · simp only [RegUpd.v_write,State.addWithCarry]

theorem lookup_z_output_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hsize : 1720≤size) (zero : s.gpr .x3=0) :
    WP isa (.block lookupZOutputCode) s fun t =>
      wordsVal t.mem base 1648 9=(if s.gpr .x2=0 then 0 else 1) ∧
      KeepRegs [.x4,.x16] s t ∧ Outside base 1648 72 s.mem t.mem ∧ t.v=s.v := by
  rw [lookupZOutputCode,WP.block_append_iff]
  refine WP.mono (lookup_z_flag_ok s zero) fun u ⟨value,ku,vu⟩ => ?_
  have hsu := hs.of_keeps ku (by decide)
  have uz : u.gpr .x3=0 := (ku.gpr .x3 (by decide)).trans zero
  refine WP.mono (storesR_any_vectors lookupZRegs hsu.ptrW (by simpa only [show lookupZRegs.length=9 from rfl] using hsize)
    (by decide)) fun t ⟨stored,kt,ot,vt⟩ => ?_
  simp only [show lookupZRegs.length=9 from rfl,Nat.reduceMul] at stored ot
  have regval : regsVal u lookupZRegs=(if s.gpr .x2=0 then 0 else 1) := by
    simp only [lookupZRegs,regsVal,uz,value,Nat.mul_zero,Nat.add_zero]
    by_cases h : s.gpr .x2=0 <;> simp only [h,ite_true,ite_false] <;> rfl
  exact ⟨stored.trans regval,(Keeps.regs ku).trans (kt.mono (by simp)),by rw [ku.mem] at ot; exact ot,vt.trans vu⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

def lookupVec (i : Nat) : VReg := lookupAccs.getD i .v0
def lookupOutputCode : List Instr := (outerBlock142.drop 618).take 22

theorem lookupOutput_split : lookupOutputCode=([.addImm .x .x17 .x0 1504] : List Instr)++
    (lookupVectorStores lookupVec 9++lookupZOutputCode) := by lit_decide

theorem lookup_output_pointer (s : State) :
    WP isa (.block [.addImm .x .x17 .x0 1504]) s fun t =>
      t.gpr .x17=s.gpr .x0+BitVec.ofNat 64 1504 ∧ Keeps [.x17] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,show (1504 : Nat)<4096 from by decide,
    ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨True.intro,⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),rfl,rfl,rfl,rfl⟩,rfl⟩

theorem lookup_output_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hsize : 1720≤size) (zero : s.gpr .x3=0) :
    WP isa (.block lookupOutputCode) s fun t =>
      (∀j<18,word t.mem base (1504+8*j)=vdword (s.v (lookupVec (j/2))) (j%2)) ∧
      wordsVal t.mem base 1648 9=(if s.gpr .x2=0 then 0 else 1) ∧
      KeepRegs [.x4,.x16,.x17] s t ∧ Outside base 1504 216 s.mem t.mem ∧ t.v=s.v := by
  rw [lookupOutput_split,WP.block_append_iff]
  refine WP.mono (lookup_output_pointer s) fun u ⟨ptr,ku,vu⟩ => ?_
  have hsu : Scr u base size := hs.of_keeps ku (by decide)
  have up : u.gpr .x17=VG.Proof.Mont.off base 1504 := by rw [ptr,hs.x0]
  rw [WP.block_append_iff]
  refine WP.mono (lookup_vector_stores_ok lookupVec hsu up 9 (by omega_arith)) fun v ⟨xy,kv,vv,ov⟩ => ?_
  have hsv : Scr v base size := hsu.of_keepRegs kv (by simp)
  have vz : v.gpr .x3=0 := (kv.gpr .x3 (by simp)).trans ((ku.gpr .x3 (by decide)).trans zero)
  refine WP.mono (lookup_z_output_ok hsv hsize vz) fun t ⟨z,kt,ot,vt⟩ => ?_
  rw [kv.gpr .x2 (by simp),ku.gpr .x2 (by decide)] at z
  refine ⟨?_,z,((Keeps.regs ku).mono (by decide)).trans ((kv.mono (by simp)).trans (kt.mono (by decide))),?_,vt.trans (vv.trans vu)⟩
  · intro j hj
    rw [ot.word (by omega_arith) (by omega_arith),xy j hj,vu]
  · simp only [Nat.reduceMul] at ov
    rw [ku.mem] at ov
    exact (ov.mono (by decide) (by decide)).trans (ot.mono (by decide) (by decide))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

def lookupInitCode : List Instr := [
  .vop (.movi0 .v0),.vop (.movi0 .v1),.vop (.movi0 .v2),.vop (.movi0 .v3),
  .vop (.movi0 .v4),.vop (.movi0 .v5),.vop (.movi0 .v6),.vop (.movi0 .v7),.vop (.movi0 .v16),
  .movz .x .x3 0 0,.movz .x .x4 1 0,.subs .x .x16 .x2 .x3,
  .cselc .x .x4 .x4 .x3 .eq,.vop (.ins .d2 .v4 1 .x4)]

theorem lookup_init_source : lookupInitCode=(outerBlock142.drop 76).take 14 := by lit_decide

theorem lookup_init_ok (s : State) :
    WP isa (.block lookupInitCode) s fun t =>
      t.gpr .x3=0 ∧
      t.v .v4=(if s.gpr .x2=0 then ofVDwords 0 1 else 0) ∧
      (∀r∈[VReg.v0,.v1,.v2,.v3,.v5,.v6,.v7,.v16],t.v r=0) ∧
      VKeep [.x3,.x4,.x16] [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v16] s t := by
  have zf (u : State) (a : Word) : (u.addWithCarry .x .x16 a (~~~(0#64)) true).zf=decide (a=0#64) := by
    change decide (addCarry a (~~~(0#64)) true=0#64)=decide (a=0#64)
    have hz : addCarry a (~~~(0#64)) true=a := by
      change a+~~~(0#64)+1#64=a
      rw [BitVec.add_assoc,show ~~~(0#64)+1#64=0#64 from rfl]
      exact BitVec.add_zero a
    rw [hz]
  have va (u : State) (a b : Word) (c : Bool) : (u.addWithCarry .x .x16 a b c).v=u.v := rfl
  apply WP.of_runBlock
  simp only [lookupInitCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,VOp.eval,Option.map_some,
    Size.bits,Nat.mul_zero,Nat.reduceLT,RegUpd.gpr_setV,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
    va,show BitVec.setWidth 64 (0 : BitVec 16)=0#64 from rfl,
    show BitVec.setWidth 64 (1 : BitVec 16)=1#64 from rfl,RegUpd.v_setV,RegUpd.v_write,CondCode.holds,BitVec.setWidth_eq,
    reduceCtorEq,ite_true,ite_false,BitVec.shiftLeft_zero,zf,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,?_,?_,⟨?_,?_,?_,?_,?_,?_⟩⟩
  · change setLane 0 64 1 (if decide (s.gpr .x2=0#64)=true then 1#64 else 0#64)=
      (if s.gpr .x2=0#64 then ofVDwords 0 1 else 0)
    by_cases hc : s.gpr .x2=0#64 <;> simp only [hc,decide_true,decide_false,ite_true,ite_false] <;> rfl
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setV,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,hr.1,hr.2.1,hr.2.2,ite_false]
  · simp only [RegUpd.mem_setV,RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_setV,RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_setV,RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_setV,RegUpd.sp_write,RegUpd.sp_addWithCarry]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.v_setV,RegUpd.v_write,va,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,
      hr.2.2.2.2.1,hr.2.2.2.2.2.1,hr.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.1,hr.2.2.2.2.2.2.2.2,ite_false]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def lookupIdentity (j : Nat) : BitVec 128 := if j=4 then ofVDwords 0 1 else 0

def lookupClob : List Reg := [.x3,.x4,.x16,.x17]

theorem lookup_split : lookupCode=lookupInitCode++(lookupEntriesCode++lookupOutputCode) := by lit_decide

private theorem lookup_magnitude_zero (d : Nat) (hd : d≤16) :
    (BitVec.ofNat 64 d=(0 : BitVec 64)) ↔ d=0 := by
  constructor
  · intro e
    have he := congrArg BitVec.toNat e
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_arith : d<2^64),show (0 : BitVec 64).toNat=0 from rfl] using he
  · intro e; rw [e]; rfl

private theorem lookup_identity_word (j : Nat) (hj : j<18) :
    vdword (lookupIdentity (j/2)) (j%2)=(if j=9 then 1 else 0) := by
  by_cases div : j/2=4
  · have hc : j=8 ∨ j=9 := by omega_arith
    rcases hc with rfl|rfl <;> simp only [lookupIdentity,Nat.reduceDiv,Nat.reduceMod,ite_true,
      vdword_ofVDwords_0,vdword_ofVDwords_1] <;> decide
  · have ne : j≠9 := by omega_arith
    simp only [lookupIdentity,div,ite_false,ne,vdword_zero]

theorem lookup_ok {s : State} {base table : Addr} {size d : Nat}
    (hs : Scr s base size) (hsize : 1720≤size) (ht : LookupTableReadable s table)
    (hd : d≤16) (digit : s.gpr .x2=BitVec.ofNat 64 d) :
    WP isa lookupProgram s fun t =>
      (∀j<18,word t.mem base (1504+8*j)=(if d=0 then (if j=9 then 1 else 0)
        else word s.mem table (lookupEntryOffset d+8*j))) ∧
      wordsVal t.mem base 1648 9=(if d=0 then 0 else 1) ∧
      KeepRegs lookupClob s t ∧ Outside base 1504 216 s.mem t.mem := by
  rw [lookupProgram,lookup_split,WP.block_append_iff]
  refine WP.mono (lookup_init_ok s) fun u ⟨zero,v4,others,ku⟩ => ?_
  have initial : ∀j(hj : j<9),u.v lookupAccs[j]=(if d=0 then lookupIdentity j else 0) := by
    intro j hj
    have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega_arith
    rw [digit] at v4
    simp only [lookup_magnitude_zero d hd] at v4
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | simpa only [lookupAccs,List.getElem_cons_succ,List.getElem_cons_zero,lookupIdentity,ite_true] using v4
      | simp only [lookupAccs,List.getElem_cons_succ,List.getElem_cons_zero,lookupIdentity,
          Nat.reduceEqDiff,ite_false,ite_self]
        apply others
        decide
  have tableU : LookupTableReadable u table :=
    ⟨(ku.gpr .x26 (by decide)).trans ht.reg,by intro j hj; rw [ku.rd,ku.wr]; exact ht.read j hj⟩
  rw [WP.block_append_iff]
  refine WP.mono (lookup_scan_sixteen hd ((ku.gpr .x2 (by decide)).trans digit) zero tableU lookupIdentity initial)
    fun w ⟨selected,kw⟩ => ?_
  have kbefore : VKeep lookupClob (.v17::.v18::lookupAccs) s w :=
    (ku.mono (by decide) (by decide)).trans (kw.mono (by decide) (by simp))
  have hsw : Scr w base size := hs.of_keeps kbefore.keeps (by decide)
  have wz : w.gpr .x3=0 := (kw.gpr .x3 (by decide)).trans zero
  refine WP.mono (lookup_output_ok hsw hsize wz) fun t ⟨words,z,kt,ot,_⟩ => ?_
  rw [kbefore.gpr .x2 (by decide),digit] at z
  simp only [lookup_magnitude_zero d hd] at z
  refine ⟨?_,z,(Keeps.regs kbefore.keeps).trans (kt.mono (by decide)),by rw [kbefore.mem] at ot; exact ot⟩
  intro j hj
  have hj2 : j/2<9 := by omega_arith
  have sv := selected (j/2) hj2
  rw [ku.mem] at sv
  have vr : lookupVec (j/2)=lookupAccs[j/2] := by
    exact (List.getElem_eq_getD (l:=lookupAccs) (i:=j/2) (h:=hj2) VReg.v0).symm
  have e := words j hj
  rw [vr,sv] at e
  by_cases h : d=0
  · simp only [h,ite_true] at e ⊢
    rw [lookup_identity_word j hj] at e
    exact e
  · simp only [h,ite_false] at e ⊢
    rw [vdword_read16 _ _ (by omega_arith : j%2<2),VG.Offset.add_ofNat_add_ofNat] at e
    have index : lookupEntryOffset d+16*(j/2)+8*(j%2)=lookupEntryOffset d+8*j := by omega_arith
    simpa only [VG.Proof.Mont.word,index] using e

end VG.Proof.Weierstrass.AArch64.P521Native
