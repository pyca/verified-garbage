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



/-! ## After the arguments are in place

The lemmas below are about any state `t` with the helper's arguments in
`r3`–`r11` (`ctx`, `rounds`, `counter`, `y`, `src`, `src_n`, `dst`, `n`,
`scratch`), as `Wrapper.headState` leaves them, and `prep t`, which also has
the extra registers saved and the core's arguments set. -/

def prep (t : State) : State := Wrapper.restState t

theorem prepared_eq (s : State) : prepared s=prep (Wrapper.headState s) := rfl

theorem prep_frame (t : State) : Frame [⟨t.gpr .r11+152,16⟩] t.mem (prep t).mem :=
  Wrapper.rest_frame t


theorem prep_saved (t : State) :
    Spill.Saved ((prep t).gpr .r9) t.gpr Impl.AesGcm.PPC64LE.SplitBlocks.extraSaved (prep t).mem :=
  Wrapper.rest_saved t


theorem prep_preserved (t : State) :
    ∀ r ∈ preserved, (Wrapper.restoredBase (prep t) t.gpr).gpr r=t.gpr r := by
  intro r hr
  have hf : ∀ r ∈ preserved, r≠.r7 ∧ r≠.r8 ∧ r≠.r9 := by decide
  obtain ⟨a,b,c⟩ := hf r hr
  simp only [Wrapper.restoredBase,prep,Wrapper.restState,Wrapper.configState,
    RegUpd.gpr_write,a,b,c,ite_false]
  by_cases h17 : r=.r17
  · subst r; simp only [reduceCtorEq,ite_false,ite_true]
  · by_cases h19 : r=.r19
    · subst r; simp only [reduceCtorEq,ite_false,ite_true]
    · simp only [h17,h19,ite_false]


theorem prep_block {t : State} {r : Region} {p : Addr} (hd : r.Disjoint ⟨t.gpr .r11,2112⟩)
    (hp : Region.Sub (⟨p,16⟩ : Region) r) :
    Spec.Gcm.blockAt (prep t).mem p=Spec.Gcm.blockAt t.mem p := by
  apply Blocks.block_frame (prep_frame t)
  intro q hq
  rw [List.mem_singleton] at hq
  subst q
  exact (hd.sub_left hp).sub_right (Offset.sub_base _ (d := 152) (n := 16) (k := 2112) (by decide))


theorem prep_cipher {t : State} {n count nr : Nat} (lay : Wrapper.Layout (prep t) n count) (hnr : nr<15) :
    Spec.Gcm.ctxCiph (prep t).mem (t.gpr .r3) nr=Spec.Gcm.ctxCiph t.mem (t.gpr .r3) nr := by
  apply Blocks.ctxCipher_frame (prep_frame t) _ hnr
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact (lay.wrapper.scratch (Blocks.coreKey (Blocks.wrapperView (prep t))) (by simp)).sub_right
    (Offset.sub_base _ (d := 152) (n := 16) (k := 2112) (by decide))


theorem prep_plain {t : State} {n count i : Nat} (lay : Wrapper.Layout (prep t) n count) (hi : i<n) :
    Wrapper.plain (prep t) count i=
      if i<count then Spec.Gcm.blockAt t.mem (t.gpr .r7+BitVec.ofNat 64 (16*i))
      else Spec.Gcm.blockAt t.mem (t.gpr .r9+BitVec.ofNat 64 (16*i)) := by
  unfold Wrapper.plain
  by_cases hic : i<count
  · rw [ite_eq_left hic,ite_eq_left hic]
    exact prep_block (r := sourceRegion (prep t) count)
      (lay.disjoint ⟨(prep t).gpr .r9,2112⟩ (by simp [Blocks.wrapperFullWrites]))
      (Offset.sub_base _ (d := 16*i) (n := 16) (k := 16*count) (by omega))
  · rw [ite_eq_right hic,ite_eq_right hic]
    exact prep_block (r := Blocks.coreData (Blocks.wrapperView (prep t)) n)
      (lay.wrapper.scratch _ (by simp))
      (Offset.sub_base _ (d := 16*i) (n := 16) (k := 16*n) (by omega))



def originalView (t : State) : State := (t.write .r17 (t.gpr .r7)).write .r7 (t.gpr .r9)


theorem prep_blocks {t : State} {n count : Nat} (lay : Wrapper.Layout (prep t) n count) :
    Wrapper.blocks (prep t) count 0 n=Spec.Gcm.blocksAt t.mem (t.gpr .r7) count ++
      (Spec.Gcm.blocksAt t.mem (t.gpr .r9) n).drop count := by
  have he : Wrapper.blocks (prep t) count 0 n=Wrapper.blocks (originalView t) count 0 n := by
    unfold Wrapper.blocks
    apply List.map_congr_left
    intro i hi
    simp only [Nat.zero_add]
    change Wrapper.plain (prep t) count i=(if i<count then
      Spec.Gcm.blockAt t.mem (t.gpr .r7+BitVec.ofNat 64 (16*i))
      else Spec.Gcm.blockAt t.mem (t.gpr .r9+BitVec.ofNat 64 (16*i)))
    exact prep_plain lay (List.mem_range.mp hi)
  rw [he,Wrapper.blocks_spec _ _ _ lay.bound]
  rfl


theorem prep_counter {t : State} {n count : Nat} (lay : Wrapper.Layout (prep t) n count) :
    Spec.Gcm.blockAt (prep t).mem (t.gpr .r5)=Spec.Gcm.blockAt t.mem (t.gpr .r5) :=
  prep_block (r := Blocks.coreCounter (Blocks.wrapperView (prep t)))
    (lay.wrapper.scratch _ (by simp)) (fun _ h => h)


theorem prep_y {t : State} {n count : Nat} (lay : Wrapper.Layout (prep t) n count) :
    Spec.Gcm.blockAt (prep t).mem (t.gpr .r6)=Spec.Gcm.blockAt t.mem (t.gpr .r6) :=
  prep_block (r := Blocks.coreY (Blocks.wrapperView (prep t)))
    (lay.wrapper.scratch _ (by simp)) (fun _ h => h)


theorem prep_h {t : State} {n count : Nat} (lay : Wrapper.Layout (prep t) n count) :
    Spec.Gcm.ctxH (prep t).mem (t.gpr .r3)=Spec.Gcm.ctxH t.mem (t.gpr .r3) :=
  prep_block (r := Blocks.coreKey (Blocks.wrapperView (prep t)))
    (lay.wrapper.scratch _ (by simp)) (Offset.sub_base _ (d := 240) (n := 16) (k := 256) (by decide))


theorem prep_ciphertext {t : State} {n count nr : Nat} (lay : Wrapper.Layout (prep t) n count) (hnr : nr<15) :
    Wrapper.ciphertext (prep t) nr count n=Spec.Gcm.ctr32 (Spec.Gcm.ctxCiph t.mem (t.gpr .r3) nr)
      (Spec.Gcm.blockAt t.mem (t.gpr .r5)) (Spec.Gcm.blocksAt t.mem (t.gpr .r7) count ++
        (Spec.Gcm.blocksAt t.mem (t.gpr .r9) n).drop count) := by
  change Spec.Gcm.ctr32 (Spec.Gcm.ctxCiph (prep t).mem (t.gpr .r3) nr)
    (Spec.Gcm.blockAt (prep t).mem (t.gpr .r5)) (Wrapper.blocks (prep t) count 0 n)=_
  rw [prep_cipher lay hnr,prep_counter lay,prep_blocks lay]

def toArgsState (s : State) : State :=
  ((((((s.write .r11 (s.gpr .r10)).write .r10 (s.gpr .r7)).write .r9 (s.gpr .r8)).write
    .r8 (s.gpr .r7)).write .r7 (s.gpr .r6)).write .r6 (s.gpr .r5)).write .r5 (s.gpr .r5+32)

theorem to_pre (s : State) (hs : (Proof.Gcm.decryptBlocksToContract PPC64LE.abi).pre s) :
    Wrapper.Layout (prep (toArgsState s)) (s.gpr .r7).toNat (s.gpr .r7).toNat ∧
    ((s.gpr .r4).toNat=10 ∨ (s.gpr .r4).toNat=12 ∨ (s.gpr .r4).toNat=14) ∧
    Covers [⟨s.gpr .r10,2112⟩] s.wr := by
  sig_eval [Proof.Gcm.decryptBlocksToContract,Proof.Gcm.decryptBlocksToSig,Proof.Gcm.decryptBlocksToPre,
    PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop] at hs
  obtain ⟨hrd,hwr,dCS,dCD,dCW,dSR,dSD,dSW,dRD,dRW,dDW,_,_,fR,fD,fW,hnr,h97⟩ := hs
  rw [h97] at hwr dCD dSD dRD dDW fD
  rw [Nat.mul_comm (s.gpr .r7).toNat 16] at hrd hwr dCD dSD dRD dDW fD dSR dRW fR
  have sC : Region.Sub (⟨s.gpr .r5+32,16⟩ : Region) ⟨s.gpr .r5,48⟩ :=
    Offset.sub_base _ (d := 32) (n := 16) (k := 48) (by decide)
  have sY : Region.Sub (⟨s.gpr .r5,16⟩ : Region) ⟨s.gpr .r5,48⟩ := Region.sub_prefix (by decide)
  have sK : Region.Sub (⟨s.gpr .r10+64,2048⟩ : Region) ⟨s.gpr .r10,2112⟩ :=
    Offset.sub_base _ (d := 64) (n := 2048) (k := 2112) (by decide)
  have dCY : Region.Disjoint (⟨s.gpr .r5+32,16⟩ : Region) ⟨s.gpr .r5,16⟩ :=
    Offset.disjoint_base _ (d := 32) (n := 16) (k := 16) (by decide) (by decide)
  refine ⟨⟨⟨⟨?_,?_,?_,?_,?_,?_,?_,by omega⟩,?_,?_,?_⟩,Nat.le_refl _,?_,?_,?_⟩,hnr,?_⟩
  · change Covers [⟨s.gpr .r3,256⟩] (s.rd++s.wr)
    rw [hrd]
    exact Covers.of_mem (by simp)
  · change Covers [⟨s.gpr .r5+32,16⟩,⟨s.gpr .r5,16⟩,⟨s.gpr .r8,16*(s.gpr .r7).toNat⟩,
      ⟨s.gpr .r10+64,2048⟩] s.wr
    rw [hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨s.gpr .r5,48⟩,by simp,32,rfl,by change 32+16≤48; decide⟩
    · exact ⟨⟨s.gpr .r5,48⟩,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+16≤48; decide⟩
    · exact ⟨⟨s.gpr .r8,16*(s.gpr .r7).toNat⟩,by simp,0,by exact (BitVec.add_zero _).symm,by omega⟩
    · exact ⟨⟨s.gpr .r10,2112⟩,by simp,64,rfl,by change 64+2048≤2112; decide⟩
  · intro r hr
    change r ∈ [⟨s.gpr .r3,256⟩,⟨s.gpr .r5+32,16⟩,⟨s.gpr .r5,16⟩,⟨s.gpr .r8,16*(s.gpr .r7).toNat⟩] at hr
    change r.Disjoint ⟨s.gpr .r10+64,2048⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [dCW.sub_right sK,(dSW.sub_left sC).sub_right sK,(dSW.sub_left sY).sub_right sK,dDW.sub_right sK]
  · intro r hr
    change r ∈ [⟨s.gpr .r3,256⟩,⟨s.gpr .r5+32,16⟩,⟨s.gpr .r5,16⟩] at hr
    change r.Disjoint ⟨s.gpr .r8,16*(s.gpr .r7).toNat⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [dCD,dSD.sub_left sC,dSD.sub_left sY]
  · exact dCS.sub_right sC
  · exact dCS.sub_right sY
  · exact dCY
  · change Covers [⟨s.gpr .r10,64⟩] s.wr
    rw [hwr]
    exact Covers.of_sub (fun r hr => by
      rw [List.mem_singleton] at hr
      subst r
      exact ⟨⟨s.gpr .r10,2112⟩,by simp,0,by exact (BitVec.add_zero _).symm,by change 0+64≤2112; decide⟩)
  · intro r hr
    change r ∈ [⟨s.gpr .r3,256⟩,⟨s.gpr .r5+32,16⟩,⟨s.gpr .r5,16⟩,⟨s.gpr .r8,16*(s.gpr .r7).toNat⟩] at hr
    change r.Disjoint ⟨s.gpr .r10,2112⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [dCW,dSW.sub_left sC,dSW.sub_left sY,dDW]
  · exact fD
  · simp only [prep,toArgsState,Wrapper.restState,Wrapper.configState,RegUpd.gpr_write,
      reduceCtorEq,ite_true,ite_false,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · change InRegions (s.rd++s.wr) (s.gpr .r6) (16*(s.gpr .r7).toNat)
    rw [hrd]
    exact ⟨_,List.mem_append_left _ (by simp),Region.contains_self _ _⟩
  · intro r hr
    change r ∈ [⟨s.gpr .r10,2112⟩,⟨s.gpr .r8,16*(s.gpr .r7).toNat⟩,⟨s.gpr .r5+32,16⟩,⟨s.gpr .r5,16⟩] at hr
    change (⟨s.gpr .r6,16*(s.gpr .r7).toNat⟩ : Region).Disjoint r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [dRW,dRD,(dSR.sub_left sC).symm,(dSR.sub_left sY).symm]
  · rw [hwr]
    exact Covers.of_mem (by simp)

end VG.Proof.AesGcm.PPC64LE.SplitBlocks.Contract
