module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Probe
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec

meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Spec.MlKem

/-! # Construct the parser constants with the measured emitted instructions -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64.Rej8
open VG.Proof.Rc4.AArch64

def vectorConsts : List Instr :=
 maskVec .v16 [0,1,2,255,3,4,5,255,6,7,8,255,9,10,11,255] ++
 maskVec .v17 [255,15,0,0,255,15,0,0,255,15,0,0,255,15,0,0] ++
 maskVec .v20 [1,1,2,1,4,1,8,1,16,1,32,1,64,1,128,1] ++
 [.movz .x .x9 3329 0,.vop (.dup .h8 .v19 .x9),.vop (.movi0 .v21)]

theorem gatherIndex_value : gatherIndex=0xff0b0a09ff080706ff050403ff020100#128 := by
  apply vbyte_ext
  exact (by decide +kernel : ∀e<16,vbyte gatherIndex e=vbyte 0xff0b0a09ff080706ff050403ff020100#128 e)

theorem vectorConsts_ok (s : State) : WP isa (.block vectorConsts) s fun u =>
    Keep [.x9] s u ∧ u.mem=s.mem ∧ Constants u := by
  dsimp [vectorConsts,maskVec,VG.Impl.MlKem.AArch64.movImm]
  rrun [RegUpd.sp_write,RegUpd.sp_setV]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · refine ⟨?_,rfl,rfl,rfl,?_⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp [State.write,State.setV,hr]
    · intro r hr
      have hn : r≠.v16 ∧ r≠.v17 ∧ r≠.v19 ∧ r≠.v20 ∧ r≠.v21 := by
        simp only [VG.AArch64.preservedV,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      simp only [RegUpd.v_write,RegUpd.v_setV,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,ite_false]
  · rw [gatherIndex_value]
    rfl
  · rfl
  · exact (by decide +kernel : ∀i<8,vhalf 0x0d010d010d010d010d010d010d010d01#128 i=3329)
  · exact (by decide +kernel : ∀i<8,vhalf 0x01800140012001100108010401020101#128 i=BitVec.ofNat 16 (256+2^i))
  · exact (by decide +kernel : ∀i<8,vhalf 0#128 i=0)


theorem address_ok (s : State) :
    WP isa (.block [.adrSym .x16 "VG_MLKEM_REJ_SHUFFLE"]) s fun u =>
      Only [.x16] s u ∧ u.gpr .x16=u.syms "VG_MLKEM_REJ_SHUFFLE" ∧ u.v=s.v := by
  refine WP.cons rfl (wp_nil ⟨?_,rfl,rfl⟩)
  refine ⟨?_,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  simp only [State.write,hr,ite_false]

theorem constants_ok (s : State) (hw : InRegions s.wr (s.gpr .x19+1408) 8) :
    WP isa (.block rejConsts) s fun u =>
      Keep [.x9,.x16] s u ∧ Constants u ∧
      u.mem=s.mem.writeW (s.gpr .x19+1408) (0 : BitVec 64) ∧
      u.gpr .x16=u.syms "VG_MLKEM_REJ_SHUFFLE" := by
  rw [show rejConsts=vectorConsts++[.movz .x .x9 0 0,.str .x .x9 .x19 1408,
    .adrSym .x16 "VG_MLKEM_REJ_SHUFFLE"] from rfl,WP.block_append_iff]
  refine WP.mono (vectorConsts_ok s) fun a ⟨ha,ham,hac⟩ => ?_
  have tail : WP isa (.block [.movz .x .x9 0 0,.str .x .x9 .x19 1408,
      .adrSym .x16 "VG_MLKEM_REJ_SHUFFLE"]) a fun u =>
      Keep [.x9,.x16] a u ∧
      u.mem=a.mem.writeW (a.gpr .x19+1408) (0 : BitVec 64) ∧
      u.gpr .x16=u.syms "VG_MLKEM_REJ_SHUFFLE" := by
    refine wp_movz fun b hb eb => wp_strx (a := a.gpr .x19+1408) (by decide)
      (by rw [hb.gpr .x19 (by decide)]; rfl)
      (by rw [hb.wr,ha.wr,ha.get .x19]; exact hw) fun c hc => ?_
    refine WP.mono (address_ok c) fun u ⟨hu,haddr,hv⟩ => ?_
    refine ⟨((hb.keep.trans hc.keep).trans hu.keep).mono (by decide),?_,haddr⟩
    · rw [hu.mem,hc.mem,eb,hb.mem]
      rfl
  refine WP.mono (WP.keepV (by decide) tail) fun u ⟨⟨hk,hm,hs⟩,hv⟩ => ?_
  refine ⟨(ha.trans hk).mono (by decide),?_,?_,?_⟩
  · exact ⟨by rw [hv]; exact hac.index,by rw [hv]; exact hac.mask,
      by simpa only [hv] using hac.q,by simpa only [hv] using hac.weights,
      by simpa only [hv] using hac.zero⟩
  · rw [hm,ham,ha.get .x19]
  · exact hs

end VG.Proof.MlKem.AArch64.Rej8
