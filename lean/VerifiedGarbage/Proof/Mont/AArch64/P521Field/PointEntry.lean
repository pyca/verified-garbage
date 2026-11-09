module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeEntry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Pointer setup for the fused ordinary-field point kernels. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (insCode lane)
open VG.Proof.Weierstrass.AArch64.Mont (exec_ins)

def doubleSetup : List Instr := [
  .vop (.ins .d2 .v25 0 .x0),
  .addImm .x .x28 .x0 4080,
  .add .x .x26 .x0 .x1,
  .add .x .x27 .x0 .x2]

def mixedSetup : List Instr := [
  .vop (.ins .d2 .v25 0 .x0),
  .vop (.ins .d2 .v24 0 .x30),
  .addImm .x .x30 .x0 4080,
  .add .x .x26 .x0 .x1,
  .add .x .x27 .x0 .x2,
  .add .x .x28 .x0 .x3]

theorem doubleEntry_eq : doubleFnBlocks.flatten.take 14=insCode nativeSaved 0++doubleSetup := by decide

theorem mixedEntry_eq : mixedFnBlocks.flatten.take 16=insCode nativeSaved 0++mixedSetup := by decide

theorem double_setup_ok (s : State) :
    WP isa (.block doubleSetup) s fun t =>
      t.gpr .x26=s.gpr .x0+s.gpr .x1 ∧ t.gpr .x27=s.gpr .x0+s.gpr .x2 ∧
      t.gpr .x28=s.gpr .x0+BitVec.ofNat 64 4080 ∧
      (t.v .v25).extractLsb' 0 64=s.gpr .x0 ∧ Keeps [.x26,.x27,.x28] s t ∧
      (∀d,d≠.v25 → t.v d=s.v d) := by
  apply WP.of_runBlock
  simp only [doubleSetup,runBlock_cons,exec_ins (by decide : 0<2),runStep_some,runBlock_nil,
    reduceExec,read_x,RegUpd.gpr_write,RegUpd.gpr_setV,RegUpd.v_write,RegUpd.v_setV,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,show (4080 : Nat)<4096 from by decide,
    Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,True.intro,True.intro,?_,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · exact VG.Proof.Weierstrass.AArch64.Mont.extract_setLane _ _ (by decide : 0<2) (by decide : 0<2)
  · reg_keeps <;> simp only [RegUpd.gpr_setV]
  · simp only [RegUpd.mem_write,RegUpd.mem_setV]
  · simp only [RegUpd.rd_write,RegUpd.rd_setV]
  · simp only [RegUpd.wr_write,RegUpd.wr_setV]
  · simp only [RegUpd.sp_write,RegUpd.sp_setV]
  · intro d hd
    simp only [hd,ite_false]

theorem mixed_setup_ok (s : State) :
    WP isa (.block mixedSetup) s fun t =>
      t.gpr .x26=s.gpr .x0+s.gpr .x1 ∧ t.gpr .x27=s.gpr .x0+s.gpr .x2 ∧
      t.gpr .x28=s.gpr .x0+s.gpr .x3 ∧ t.gpr .x30=s.gpr .x0+BitVec.ofNat 64 4080 ∧
      (t.v .v25).extractLsb' 0 64=s.gpr .x0 ∧ (t.v .v24).extractLsb' 0 64=s.gpr .x30 ∧
      Keeps [.x26,.x27,.x28,.x30] s t ∧ (∀d,d≠.v25 → d≠.v24 → t.v d=s.v d) := by
  apply WP.of_runBlock
  simp only [mixedSetup,runBlock_cons,exec_ins (by decide : 0<2),runStep_some,runBlock_nil,
    reduceExec,read_x,RegUpd.gpr_write,RegUpd.gpr_setV,RegUpd.v_write,RegUpd.v_setV,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,show (4080 : Nat)<4096 from by decide,
    Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,True.intro,True.intro,True.intro,?_,?_,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · exact VG.Proof.Weierstrass.AArch64.Mont.extract_setLane _ _ (by decide : 0<2) (by decide : 0<2)
  · exact VG.Proof.Weierstrass.AArch64.Mont.extract_setLane _ _ (by decide : 0<2) (by decide : 0<2)
  · reg_keeps <;> simp only [RegUpd.gpr_setV]
  · simp only [RegUpd.mem_write,RegUpd.mem_setV]
  · simp only [RegUpd.rd_write,RegUpd.rd_setV]
  · simp only [RegUpd.wr_write,RegUpd.wr_setV]
  · simp only [RegUpd.sp_write,RegUpd.sp_setV]
  · intro d h25 h24
    simp only [h25,h24,ite_false]

theorem double_entry_ok (s : State) :
    WP isa (.block (doubleFnBlocks.flatten.take 14)) s fun t =>
      t.gpr .x26=s.gpr .x0+s.gpr .x1 ∧ t.gpr .x27=s.gpr .x0+s.gpr .x2 ∧
      t.gpr .x28=s.gpr .x0+BitVec.ofNat 64 4080 ∧
      (t.v .v25).extractLsb' 0 64=s.gpr .x0 ∧
      (∀i (h : i<nativeSaved.length),lane t.v i=s.gpr nativeSaved[i]) ∧
      Keeps [.x26,.x27,.x28] s t ∧ t.v .v31=s.v .v31 := by
  rw [doubleEntry_eq,WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.AArch64.P521Square.saves_ok nativeSaved 0 (s:=s) (by decide))
    fun u ⟨ku,lanes,_,vecs⟩ => ?_
  refine WP.mono (double_setup_ok u) fun t ⟨e26,e27,e28,workspace,kt,vec⟩ => ?_
  rw [ku.gpr] at e26 e27 e28 workspace
  refine ⟨e26,e27,e28,workspace,?_,⟨?_,kt.mem.trans ku.mem,kt.rd.trans ku.rd,
    kt.wr.trans ku.wr,kt.sp.trans ku.sp⟩,(vec .v31 (by decide)).trans (vecs .v31 (by decide))⟩
  · intro i hi
    have hslot : (VG.Impl.Mont.AArch64.P521Square.slot i).1≠VReg.v25 :=
      (by decide : ∀i<10,(VG.Impl.Mont.AArch64.P521Square.slot i).1≠VReg.v25) i hi
    dsimp only [lane]
    rw [vec _ hslot]
    simpa only [Nat.zero_add,lane] using lanes i hi
  · intro r hr
    exact (kt.gpr r hr).trans (congrFun ku.gpr r)

theorem mixed_entry_ok (s : State) :
    WP isa (.block (mixedFnBlocks.flatten.take 16)) s fun t =>
      t.gpr .x26=s.gpr .x0+s.gpr .x1 ∧ t.gpr .x27=s.gpr .x0+s.gpr .x2 ∧
      t.gpr .x28=s.gpr .x0+s.gpr .x3 ∧ t.gpr .x30=s.gpr .x0+BitVec.ofNat 64 4080 ∧
      (t.v .v25).extractLsb' 0 64=s.gpr .x0 ∧ (t.v .v24).extractLsb' 0 64=s.gpr .x30 ∧
      (∀i (h : i<nativeSaved.length),lane t.v i=s.gpr nativeSaved[i]) ∧
      Keeps [.x26,.x27,.x28,.x30] s t ∧ t.v .v31=s.v .v31 := by
  rw [mixedEntry_eq,WP.block_append_iff]
  refine WP.mono (VG.Proof.Mont.AArch64.P521Square.saves_ok nativeSaved 0 (s:=s) (by decide))
    fun u ⟨ku,lanes,_,vecs⟩ => ?_
  refine WP.mono (mixed_setup_ok u) fun t ⟨e26,e27,e28,e30,workspace,lr,kt,vec⟩ => ?_
  rw [ku.gpr] at e26 e27 e28 e30 workspace lr
  refine ⟨e26,e27,e28,e30,workspace,lr,?_,⟨?_,kt.mem.trans ku.mem,kt.rd.trans ku.rd,
    kt.wr.trans ku.wr,kt.sp.trans ku.sp⟩,(vec .v31 (by decide) (by decide)).trans (vecs .v31 (by decide))⟩
  · intro i hi
    have hslot : (VG.Impl.Mont.AArch64.P521Square.slot i).1≠VReg.v25 :=
      (by decide : ∀i<10,(VG.Impl.Mont.AArch64.P521Square.slot i).1≠VReg.v25) i hi
    dsimp only [lane]
    have hslot24 : (VG.Impl.Mont.AArch64.P521Square.slot i).1≠VReg.v24 :=
      (by decide : ∀i<10,(VG.Impl.Mont.AArch64.P521Square.slot i).1≠VReg.v24) i hi
    rw [vec _ hslot hslot24]
    simpa only [Nat.zero_add,lane] using lanes i hi
  · intro r hr
    exact (kt.gpr r hr).trans (congrFun ku.gpr r)

end VG.Proof.Mont.AArch64.P521Field
