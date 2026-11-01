module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealSplit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: entry argument conversion and the source cache are shared by seal proofs.
/-! # The source-prefix seal entry -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit.Prelude
open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE.SealSplit (sourceSaved)


def headState (s : State) : State :=
  (s.write .r12 s.sp).write .r11 (s.mem.readW (s.sp+232) 64)


theorem head_ok (s : State) (hr : InRegions (s.rd++s.wr) (s.sp+232) 8) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealSplit.loadWork) s (· = headState s) := by
  have ha : exec (.addSp .r12 0) s=some (s.write .r12 s.sp) := by
    simp only [exec,Nat.reducePow,Nat.reduceLT,ite_true,BitVec.add_zero]
  have hr' : InRegions ((s.write .r12 s.sp).rd++(s.write .r12 s.sp).wr)
      ((s.write .r12 s.sp).gpr .r12+BitVec.ofNat 64 232) 8 := hr
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.SealSplit.loadWork,runBlock_cons,runStep_some,runBlock_nil,ha,
    exec_load_d (n := .r12) (off := 232) (by decide) ⟨by decide,by decide⟩ hr',
    RegUpd.gpr_write_self,RegUpd.mem_write,Option.some.injEq,exists_eq_left']
  rfl


def savedState (s : State) : State :=
  {s with mem := Spill.saveMem s.mem (s.gpr .r11) s.gpr sourceSaved}


theorem save_ok (s : State)
    (hw : ∀ p ∈ sourceSaved, InRegions s.wr (s.gpr .r11+BitVec.ofNat 64 p.2) 8) :
    WP isa (.block (sourceSaved.map (fun (r,o) => Instr.store .d r .r11 o))) s (· = savedState s) := by
  change WP isa (.block (Spill.saveCode .r11 sourceSaved)) s _
  rw [← List.append_nil (Spill.saveCode .r11 sourceSaved)]
  exact Spill.save_ok (by decide) (by decide) hw (WP.block_nil rfl)


def configState (s : State) : State :=
  let p := s.gpr .r12
  let t := s.mem.readW (p+224) 64
  let u := ((s.write .r9 (s.mem.readW (p+208) 64)).write .r10 (s.mem.readW (p+216) 64)).write .r0 t
  {u with mem := (s.mem.writeW (p+96) t).writeW (p+104) (s.gpr .r11)}


theorem config_ok (s : State)
    (hr : ∀ off ∈ [208,216,224], InRegions (s.rd++s.wr) (s.gpr .r12+BitVec.ofNat 64 off) 8)
    (hw : ∀ off ∈ [96,104], InRegions s.wr (s.gpr .r12+BitVec.ofNat 64 off) 8) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealSplit.config) s (· = configState s) := by
  let a := s.write .r9 (s.mem.readW (s.gpr .r12+208#64) 64)
  let b := a.write .r10 (s.mem.readW (s.gpr .r12+216#64) 64)
  let c := b.write .r0 (s.mem.readW (s.gpr .r12+224#64) 64)
  let d : State := {c with mem := c.mem.writeW (c.gpr .r12+96) (c.gpr .r0)}
  have h216 : InRegions (a.rd++a.wr) (a.gpr .r12+BitVec.ofNat 64 216) 8 := hr 216 (by decide)
  have h224 : InRegions (b.rd++b.wr) (b.gpr .r12+BitVec.ofNat 64 224) 8 := hr 224 (by decide)
  have w96 : InRegions c.wr (c.gpr .r12+BitVec.ofNat 64 96) 8 := hw 96 (by decide)
  have w104 : InRegions d.wr (d.gpr .r12+BitVec.ofNat 64 104) 8 := hw 104 (by decide)
  rw [Impl.AesGcm.PPC64LE.SealSplit.config]
  refine WP.block_cons_iff.mpr ⟨a,?_,?_⟩
  · exact exec_load_d (s := s) (n := .r12) (off := 208) (by decide) ⟨by decide,by decide⟩ (hr 208 (by decide))
  refine WP.block_cons_iff.mpr ⟨b,?_,?_⟩
  · simpa only [a,b,RegUpd.gpr_write,RegUpd.mem_write,reduceCtorEq,ite_false] using
      exec_load_d (s := a) (n := .r12) (t := .r10) (off := 216) (by decide) ⟨by decide,by decide⟩ h216
  refine WP.block_cons_iff.mpr ⟨c,?_,?_⟩
  · simpa only [a,b,c,RegUpd.gpr_write,RegUpd.mem_write,reduceCtorEq,ite_false] using
      exec_load_d (s := b) (n := .r12) (t := .r0) (off := 224) (by decide) ⟨by decide,by decide⟩ h224
  refine WP.block_cons_iff.mpr ⟨d,?_,?_⟩
  · exact exec_store_d (s := c) (n := .r12) (off := 96) (by decide) ⟨by decide,by decide⟩ w96
  refine WP.block_cons_iff.mpr ⟨_,exec_store_d (s := d) (n := .r12) (off := 104) (by decide) ⟨by decide,by decide⟩ w104,?_⟩
  exact WP.block_nil rfl



def work (s : State) : Addr := s.mem.readW (s.sp+232) 64

def readOffsets : List Nat := [208,216,224,232]

def argOffsets : List Nat := [96,104]++readOffsets

structure Config (s : State) : Prop where
  reads : ∀ off ∈ readOffsets, InRegions (s.rd++s.wr) (s.sp+BitVec.ofNat 64 off) 8
  writes : ∀ off ∈ [96,104], InRegions s.wr (s.sp+BitVec.ofNat 64 off) 8
  workCovers : Covers [⟨work s,2560⟩] s.wr
  apart : ∀ off ∈ argOffsets, (⟨work s,2560⟩ : Region).Disjoint ⟨s.sp+BitVec.ofNat 64 off,8⟩


def state (s : State) : State := configState (savedState (headState s))


theorem ok (s : State) (cfg : Config s) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealSplit.prelude) s (· = state s) := by
  rw [Impl.AesGcm.PPC64LE.SealSplit.prelude,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (head_ok s (cfg.reads 232 (by decide))) fun h hh => ?_
  subst h
  refine WP.mono (save_ok (headState s) (by
    intro p hp
    have ho : ∀ p ∈ sourceSaved, p.2+8≤2560 := by decide
    exact cfg.workCovers _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ (ho p hp) (by have := ho p hp; omega)⟩))
    fun u hu => ?_
  subst u
  exact config_ok _ (fun off ho => cfg.reads off (by
    simp only [readOffsets,List.mem_cons,List.not_mem_nil,or_false] at ho ⊢
    rcases ho with rfl | rfl | rfl <;> simp)) cfg.writes


theorem save_frame (s : State) :
    Frame [⟨s.gpr .r11+112,16⟩] s.mem (savedState s).mem :=
  Spill.saveMem_frame (lo := 112) (n := 16) (by decide) (by decide) _ _ _


theorem config_frame (s : State) :
    Frame [⟨s.gpr .r12+96,8⟩,⟨s.gpr .r12+104,8⟩] s.mem (configState s).mem := by
  exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
    (by simp) _ (Region.contains_self _ _)


def writes (s : State) : List Region :=
  [⟨work s+112,16⟩,⟨s.sp+96,8⟩,⟨s.sp+104,8⟩]


theorem frame (s : State) : Frame (writes s) s.mem (state s).mem := by
  have hs : Frame [⟨work s+112,16⟩] s.mem (savedState (headState s)).mem := save_frame (headState s)
  have hc : Frame [⟨s.sp+96,8⟩,⟨s.sp+104,8⟩] (savedState (headState s)).mem (state s).mem :=
    config_frame (savedState (headState s))
  exact (hs.mono (by simp [writes])).trans (hc.mono (by simp [writes]))


theorem cache_read (s : State) (cfg : Config s) (off : Nat) (ho : off ∈ argOffsets) :
    (savedState (headState s)).mem.readW (s.sp+BitVec.ofNat 64 off) 64=
      s.mem.readW (s.sp+BitVec.ofNat 64 off) 64 := by
  apply (save_frame (headState s)).readW (r := ⟨s.sp+BitVec.ofNat 64 off,8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact (cfg.apart off ho).symm.sub_right (Offset.sub_base _ (d := 112) (n := 16) (k := 2560) (by decide))


theorem source_saved (s : State) (cfg : Config s) : Spill.Saved (work s) s.gpr sourceSaved (state s).mem := by
  have hs : Spill.Saved (work s) s.gpr sourceSaved (savedState (headState s)).mem := by
    intro p hp
    have h := Spill.saveMem_saved (l := sourceSaved) (by decide) (headState s).mem (work s) (headState s).gpr p hp
    have hg : (headState s).gpr p.1=s.gpr p.1 := by
      have hf : ∀ p ∈ sourceSaved, p.1≠.r11 ∧ p.1≠.r12 := by decide
      simp only [headState,RegUpd.gpr_write,(hf p hp).1,(hf p hp).2,ite_false]
    exact h.trans hg
  refine hs.frame_in (lo := 112) (n := 16) (by decide) (config_frame (savedState (headState s))) ?_
  intro r hr
  change r ∈ [⟨s.sp+96,8⟩,⟨s.sp+104,8⟩] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact (cfg.apart 96 (by decide)).sub_left (Offset.sub_base _ (d := 112) (n := 16) (k := 2560) (by decide))
  · exact (cfg.apart 104 (by decide)).sub_left (Offset.sub_base _ (d := 112) (n := 16) (k := 2560) (by decide))



theorem destination (s : State) (cfg : Config s) :
    (state s).gpr .r9=s.mem.readW (s.sp+208) 64 := by
  change (savedState (headState s)).mem.readW (s.sp+208#64) 64=_
  exact cache_read s cfg 208 (by decide)


theorem length (s : State) (cfg : Config s) :
    (state s).gpr .r10=s.mem.readW (s.sp+216) 64 := by
  change (savedState (headState s)).mem.readW (s.sp+216#64) 64=_
  exact cache_read s cfg 216 (by decide)


theorem config_arg0 (s : State) :
    (configState s).mem.readW (s.gpr .r12+96) 64=s.mem.readW (s.gpr .r12+224) 64 := by
  change ((s.mem.writeW (s.gpr .r12+96) (s.mem.readW (s.gpr .r12+224) 64)).writeW
    (s.gpr .r12+104) (s.gpr .r11)).readW (s.gpr .r12+96) 64=_
  rw [Mem.readW_writeW_sep (Offset.sep _ (d := 96) (n := 8) (e := 104) (k := 8)
    (by decide) (by decide) (by decide)) (by decide),Mem.readW_writeW_self64]


theorem config_arg1 (s : State) : (configState s).mem.readW (s.gpr .r12+104) 64=s.gpr .r11 := by
  exact Mem.readW_writeW_self64 ..


theorem tag_argument (s : State) (cfg : Config s) :
    (state s).mem.readW (s.sp+96) 64=s.mem.readW (s.sp+224) 64 :=
  (config_arg0 (savedState (headState s))).trans (cache_read s cfg 224 (by decide))


theorem work_argument (s : State) : (state s).mem.readW (s.sp+104) 64=work s :=
  config_arg1 (savedState (headState s))


theorem fields (s : State) :
    (state s).rd=s.rd ∧ (state s).wr=s.wr ∧ (state s).sp=s.sp ∧ (state s).lr=s.lr := by
  exact ⟨rfl,rfl,rfl,rfl⟩


theorem keep (s : State) : Keep [.r0,.r9,.r10,.r11,.r12] s (state s) := by
  refine ⟨fun r hr => ?_,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  obtain ⟨h0,h9,h10,h11,h12⟩ := hr
  simp only [state,configState,savedState,headState,RegUpd.gpr_write,h0,h9,h10,h11,h12,ite_false]

end VG.Proof.AesGcm.PPC64LE.SealSplit.Prelude
