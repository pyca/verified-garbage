module

public import VerifiedGarbage.Proof.Gcm.SplitBlocksContract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Wrapper
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

-- separate module: the public signature and memory layout of the source-prefix helper.
/-! # The POWER8 whole-block source-prefix contract -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SplitBlocks.Contract
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.SplitBlocks


def scratch (s : State) : Addr := s.mem.readW (s.sp+96) 64

def prepared (s : State) : State := Wrapper.restState (Wrapper.headState s)


theorem shared_pre (s : State) (hs : (Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi).pre s) :
    Wrapper.Layout (prepared s) (s.gpr .r10).toNat (s.gpr .r8).toNat ∧
    ((s.gpr .r4).toNat=10 ∨ (s.gpr .r4).toNat=12 ∨ (s.gpr .r4).toNat=14) ∧
    InRegions (s.rd++s.wr) (s.sp+96) 8 ∧ Covers [⟨scratch s,2112⟩] s.wr := by
  sig_eval [Proof.Gcm.encryptBlocksSplitContract,Proof.Gcm.encryptBlocksSplitSig,Proof.Gcm.encryptBlocksSplitPre,
    PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop] at hs
  obtain ⟨_,hrd,hwr,hkc,hky,hkd,hks,hcy,hcsrc,hcd,hcs,_,hysrc,hyd,hys,_,hsrcd,hsrcs,hds,_,_,
    hK,hC,hY,hSrc,hD,hS,hnr,hbound⟩ := hs
  rw [Nat.mul_comm (s.gpr .r10).toNat 16] at hwr hkd hcd hyd hsrcd hds hD
  rw [Nat.mul_comm (s.gpr .r8).toNat 16] at hrd hcsrc hysrc hsrcd hsrcs hSrc
  have hsub : Region.Sub (⟨scratch s+64,2048⟩ : Region) ⟨scratch s,2112⟩ :=
    Offset.sub_base _ (d := 64) (n := 2048) (k := 2112) (by decide)
  have hwork : Covers [⟨scratch s,2112⟩] s.wr := by
    rw [hwr]
    exact Covers.of_mem (by simp [scratch])
  refine ⟨⟨⟨?_,?_,?_,?_⟩,hbound,?_,?_,?_⟩,hnr,?_,hwork⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,by omega⟩
    · change Covers [⟨s.gpr .r3,256⟩] (s.rd++s.wr)
      rw [hrd]
      exact Covers.of_mem (by simp)
    · change Covers [⟨s.gpr .r5,16⟩,⟨s.gpr .r6,16⟩,⟨s.gpr .r9,16*(s.gpr .r10).toNat⟩,
        ⟨scratch s+64,2048⟩] s.wr
      rw [hwr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨s.gpr .r5,16⟩,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+16≤16; decide⟩
      · exact ⟨⟨s.gpr .r6,16⟩,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+16≤16; decide⟩
      · exact ⟨⟨s.gpr .r9,16*(s.gpr .r10).toNat⟩,by simp,0,by exact (BitVec.add_zero _).symm,by omega⟩
      · exact ⟨⟨scratch s,2112⟩,by simp [scratch],64,rfl,by change 64+2048≤2112; decide⟩
    · intro r hr
      change r ∈ [⟨s.gpr .r3,256⟩,⟨s.gpr .r5,16⟩,⟨s.gpr .r6,16⟩,⟨s.gpr .r9,16*(s.gpr .r10).toNat⟩] at hr
      change r.Disjoint ⟨scratch s+64,2048⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hks.sub_right hsub,hcs.sub_right hsub,hys.sub_right hsub,hds.sub_right hsub]
    · intro r hr
      change r ∈ [⟨s.gpr .r3,256⟩,⟨s.gpr .r5,16⟩,⟨s.gpr .r6,16⟩] at hr
      change r.Disjoint ⟨s.gpr .r9,16*(s.gpr .r10).toNat⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hkd,hcd,hyd]
    · exact hkc
    · exact hky
    · exact hcy
  · change Covers [⟨scratch s,64⟩] s.wr
    exact Covers.trans (Covers.of_sub (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact ⟨⟨scratch s,2112⟩,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+64≤2112; decide⟩)) hwork
  · intro r hr
    change r ∈ [⟨s.gpr .r3,256⟩,⟨s.gpr .r5,16⟩,⟨s.gpr .r6,16⟩,⟨s.gpr .r9,16*(s.gpr .r10).toNat⟩] at hr
    change r.Disjoint ⟨scratch s,2112⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hks,hcs,hys,hds]
  · exact hD
  · simp only [prepared,Wrapper.restState,Wrapper.configState,Wrapper.headState,RegUpd.gpr_write,
      reduceCtorEq,ite_true,ite_false,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · change InRegions (s.rd++s.wr) (s.gpr .r7) (16*(s.gpr .r8).toNat)
    rw [hrd]
    exact ⟨_,List.mem_append_left _ (by simp),Region.contains_self _ _⟩
  · intro r hr
    change r ∈ [⟨scratch s,2112⟩,⟨s.gpr .r9,16*(s.gpr .r10).toNat⟩,⟨s.gpr .r5,16⟩,⟨s.gpr .r6,16⟩] at hr
    change (⟨s.gpr .r7,16*(s.gpr .r8).toNat⟩ : Region).Disjoint r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hsrcs,hsrcd,hcsrc.symm,hysrc.symm]
  · rw [hrd]
    exact ⟨_,List.mem_append_left _ (by simp),Region.contains_self _ _⟩



theorem prepared_frame (s : State) : Frame [⟨scratch s+152,16⟩] s.mem (prepared s).mem :=
  Wrapper.rest_frame (Wrapper.headState s)


theorem prepared_saved (s : State) :
    Spill.Saved ((prepared s).gpr .r9) s.gpr Impl.AesGcm.PPC64LE.SplitBlocks.extraSaved (prepared s).mem := by
  intro p hp
  have h := Wrapper.rest_saved (Wrapper.headState s) p hp
  have hfree : ∀ p ∈ Impl.AesGcm.PPC64LE.SplitBlocks.extraSaved, p.1≠.r11 ∧ p.1≠.r12 := by decide
  have hg : (Wrapper.headState s).gpr p.1=s.gpr p.1 := by
    simp only [Wrapper.headState,RegUpd.gpr_write,(hfree p hp).1,(hfree p hp).2,ite_false]
  change (prepared s).mem.readW (scratch s+BitVec.ofNat 64 p.2) 64=s.gpr p.1
  exact h.trans hg


theorem prepared_preserved (s : State) :
    ∀ r ∈ preserved, (Wrapper.restoredBase (prepared s) s.gpr).gpr r=s.gpr r := by
  intro r hr
  have hf : ∀ r ∈ preserved, r≠.r7 ∧ r≠.r8 ∧ r≠.r9 ∧ r≠.r11 ∧ r≠.r12 := by decide
  obtain ⟨a,b,c,d,e⟩ := hf r hr
  simp only [Wrapper.restoredBase,prepared,Wrapper.restState,Wrapper.configState,Wrapper.headState,
    RegUpd.gpr_write,a,b,c,d,e,ite_false]
  by_cases h17 : r=.r17
  · subst r; simp only [reduceCtorEq,ite_false,ite_true]
  · by_cases h19 : r=.r19
    · subst r; simp only [reduceCtorEq,ite_false,ite_true]
    · simp only [h17,h19,ite_false]


theorem prepared_block {s : State} {r : Region} {p : Addr} (hd : r.Disjoint ⟨scratch s,2112⟩)
    (hp : Region.Sub (⟨p,16⟩ : Region) r) :
    Spec.Gcm.blockAt (prepared s).mem p=Spec.Gcm.blockAt s.mem p := by
  apply Blocks.block_frame (prepared_frame s)
  intro q hq
  rw [List.mem_singleton] at hq
  subst q
  exact (hd.sub_left hp).sub_right (Offset.sub_base _ (d := 152) (n := 16) (k := 2112) (by decide))


theorem prepared_cipher {s : State} {n count nr : Nat} (lay : Wrapper.Layout (prepared s) n count) (hnr : nr<15) :
    Spec.Gcm.ctxCiph (prepared s).mem (s.gpr .r3) nr=Spec.Gcm.ctxCiph s.mem (s.gpr .r3) nr := by
  apply Blocks.ctxCipher_frame (prepared_frame s) _ hnr
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact (lay.wrapper.scratch (Blocks.coreKey (Blocks.wrapperView (prepared s))) (by simp)).sub_right
    (Offset.sub_base _ (d := 152) (n := 16) (k := 2112) (by decide))


theorem prepared_plain {s : State} {n count i : Nat} (lay : Wrapper.Layout (prepared s) n count) (hi : i<n) :
    Wrapper.plain (prepared s) count i=
      if i<count then Spec.Gcm.blockAt s.mem (s.gpr .r7+BitVec.ofNat 64 (16*i))
      else Spec.Gcm.blockAt s.mem (s.gpr .r9+BitVec.ofNat 64 (16*i)) := by
  unfold Wrapper.plain
  by_cases hic : i<count
  · rw [ite_eq_left hic,ite_eq_left hic]
    exact prepared_block (r := sourceRegion (prepared s) count)
      (lay.disjoint ⟨(prepared s).gpr .r9,2112⟩ (by simp [Blocks.wrapperFullWrites]))
      (Offset.sub_base _ (d := 16*i) (n := 16) (k := 16*count) (by omega))
  · rw [ite_eq_right hic,ite_eq_right hic]
    exact prepared_block (r := Blocks.coreData (Blocks.wrapperView (prepared s)) n)
      (lay.wrapper.scratch _ (by simp))
      (Offset.sub_base _ (d := 16*i) (n := 16) (k := 16*n) (by omega))



def originalView (s : State) : State := (s.write .r17 (s.gpr .r7)).write .r7 (s.gpr .r9)


theorem prepared_blocks {s : State} {n count : Nat} (lay : Wrapper.Layout (prepared s) n count) :
    Wrapper.blocks (prepared s) count 0 n=Spec.Gcm.blocksAt s.mem (s.gpr .r7) count ++
      (Spec.Gcm.blocksAt s.mem (s.gpr .r9) n).drop count := by
  have he : Wrapper.blocks (prepared s) count 0 n=Wrapper.blocks (originalView s) count 0 n := by
    unfold Wrapper.blocks
    apply List.map_congr_left
    intro i hi
    simp only [Nat.zero_add]
    change Wrapper.plain (prepared s) count i=(if i<count then
      Spec.Gcm.blockAt s.mem (s.gpr .r7+BitVec.ofNat 64 (16*i))
      else Spec.Gcm.blockAt s.mem (s.gpr .r9+BitVec.ofNat 64 (16*i)))
    exact prepared_plain lay (List.mem_range.mp hi)
  rw [he,Wrapper.blocks_spec _ _ _ lay.bound]
  rfl


theorem prepared_counter {s : State} {n count : Nat} (lay : Wrapper.Layout (prepared s) n count) :
    Spec.Gcm.blockAt (prepared s).mem (s.gpr .r5)=Spec.Gcm.blockAt s.mem (s.gpr .r5) :=
  prepared_block (r := Blocks.coreCounter (Blocks.wrapperView (prepared s)))
    (lay.wrapper.scratch _ (by simp)) (fun _ h => h)


theorem prepared_y {s : State} {n count : Nat} (lay : Wrapper.Layout (prepared s) n count) :
    Spec.Gcm.blockAt (prepared s).mem (s.gpr .r6)=Spec.Gcm.blockAt s.mem (s.gpr .r6) :=
  prepared_block (r := Blocks.coreY (Blocks.wrapperView (prepared s)))
    (lay.wrapper.scratch _ (by simp)) (fun _ h => h)


theorem prepared_h {s : State} {n count : Nat} (lay : Wrapper.Layout (prepared s) n count) :
    Spec.Gcm.ctxH (prepared s).mem (s.gpr .r3)=Spec.Gcm.ctxH s.mem (s.gpr .r3) :=
  prepared_block (r := Blocks.coreKey (Blocks.wrapperView (prepared s)))
    (lay.wrapper.scratch _ (by simp)) (Offset.sub_base _ (d := 240) (n := 16) (k := 256) (by decide))


theorem prepared_ciphertext {s : State} {n count nr : Nat} (lay : Wrapper.Layout (prepared s) n count) (hnr : nr<15) :
    Wrapper.ciphertext (prepared s) nr count n=Spec.Gcm.ctr32 (Spec.Gcm.ctxCiph s.mem (s.gpr .r3) nr)
      (Spec.Gcm.blockAt s.mem (s.gpr .r5)) (Spec.Gcm.blocksAt s.mem (s.gpr .r7) count ++
        (Spec.Gcm.blocksAt s.mem (s.gpr .r9) n).drop count) := by
  change Spec.Gcm.ctr32 (Spec.Gcm.ctxCiph (prepared s).mem (s.gpr .r3) nr)
    (Spec.Gcm.blockAt (prepared s).mem (s.gpr .r5)) (Wrapper.blocks (prepared s) count 0 n)=_
  rw [prepared_cipher lay hnr,prepared_counter lay,prepared_blocks lay]

end VG.Proof.AesGcm.PPC64LE.SplitBlocks.Contract
