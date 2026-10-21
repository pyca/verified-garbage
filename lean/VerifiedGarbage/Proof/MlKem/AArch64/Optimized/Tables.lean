module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64

structure Tables (s : State) : Prop where
 shuffle : Rej8.TableArtifact s.mem (s.syms "VG_MLKEM_REJ_SHUFFLE")
 shuffleRead : Covers [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩] (s.rd++s.wr)
 shuffleApart : ∀r∈s.wr,(Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint r
 shuffleStack : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint (below s.sp 16)
 gamma : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA")
 gammaRead : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr)
 gammaApart : ∀r∈s.wr,(Region.mk (s.syms "VG_MLKEM_GAMMA") 512).Disjoint r
 gammaStack : (Region.mk (s.syms "VG_MLKEM_GAMMA") 512).Disjoint (below s.sp 16)
 transforms : TransformTables s

theorem Tables.frame {s t : State} (h : Tables s)
 (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hp : t.sp=s.sp)
 (hf : Frame s.wr s.mem t.mem) : Tables t := by
 refine ⟨?_,by simpa only [hs,hr,hw] using h.shuffleRead,
  by simpa only [hs,hw] using h.shuffleApart,
  by simpa only [hs,hp] using h.shuffleStack,?_,
  by simpa only [hs,hr,hw] using h.gammaRead,
  by simpa only [hs,hw] using h.gammaApart,
  by simpa only [hs,hp] using h.gammaStack,
  h.transforms.frame hs hr hw hp hf (fun _ _ h=>h)⟩
 · rw [hs]; exact h.shuffle.frame hf h.shuffleApart
 · rw [hs]; intro i hi
   rw [hf.readW (r:=⟨s.syms "VG_MLKEM_GAMMA",512⟩)
    (Offset.contains_base _ (by omega) (by omega)) h.gammaApart (by decide)]
   exact h.gamma i hi

theorem Tables.frameStack {s t : State} (h : Tables s)
 (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hp : t.sp=s.sp)
 (hf : Frame (s.wr++[below s.sp 16]) s.mem t.mem) : Tables t := by
 have ext {r : Region} (a : ∀q∈s.wr,r.Disjoint q) (b : r.Disjoint (below s.sp 16)) :
  ∀q∈s.wr++[below s.sp 16],r.Disjoint q := by
  intro q hq; rcases List.mem_append.mp hq with hq|hq
  · exact a q hq
  · rw [List.mem_singleton.mp hq]; exact b
 have sh := ext h.shuffleApart h.shuffleStack
 have ga := ext h.gammaApart h.gammaStack
 have fw := ext h.transforms.forward.2.2 h.transforms.forwardStack
 have iv := ext h.transforms.inverse.2.2 h.transforms.inverseStack
 have fa := ext h.transforms.fast.2.2 h.transforms.fastStack
 refine ⟨?_,by simpa only [hs,hr,hw] using h.shuffleRead,
  by simpa only [hs,hw] using h.shuffleApart,
  by simpa only [hs,hp] using h.shuffleStack,?_,
  by simpa only [hs,hr,hw] using h.gammaRead,
  by simpa only [hs,hw] using h.gammaApart,
  by simpa only [hs,hp] using h.gammaStack,
  ⟨⟨?_,by simpa only [hs,hr,hw] using h.transforms.forward.2.1,
    by simpa only [hs,hw] using h.transforms.forward.2.2⟩,
   ⟨?_,by simpa only [hs,hr,hw] using h.transforms.inverse.2.1,
    by simpa only [hs,hw] using h.transforms.inverse.2.2⟩,
   by simpa only [hs,hp] using h.transforms.forwardStack,
   by simpa only [hs,hp] using h.transforms.inverseStack,
   h.transforms.fast.frameFar hs hr hw hf fa,
   by simpa only [NttR.fastRegion,hs,hp] using h.transforms.fastStack⟩⟩
 · rw [hs]; exact h.shuffle.frame hf sh
 · rw [hs]; intro i hi
   rw [hf.readW (r:=⟨s.syms "VG_MLKEM_GAMMA",512⟩)
    (Offset.contains_base _ (by omega) (by omega)) ga (by decide)]
   exact h.gamma i hi
 · rw [hs]; intro i hi
   rw [hf.readW (r:=⟨s.syms "VG_MLKEM_NTT16_ZETAS",512⟩)
    (Offset.contains_base _ (by omega) (by omega)) fw (by decide)]
   exact h.transforms.forward.1 i hi
 · rw [hs]; intro i hi
   rw [hf.readW (r:=⟨s.syms "VG_MLKEM_INTT16_ZETAS",512⟩)
    (Offset.contains_base _ (by omega) (by omega)) iv (by decide)]
   exact h.transforms.inverse.1 i hi

theorem Tables.execDepth {s t : State} {c : Prog isa} {tr : List Leak}
 (h : Tables s) (he : Exec isa c s tr t) (hn : c.aarch64Depth≤1) : Tables t := by
 obtain ⟨hr,hw,hsp⟩:=VG.AArch64.Exec.rdwr he
 have hf := Frame.below_mono (VG.AArch64.Exec.frameSp he (by omega)) (b:=16) (by omega) (by decide)
 exact h.frameStack (VG.AArch64.Exec.syms he) hr hw hsp hf

theorem WP.tablesDepth {s : State} {c : Prog isa} {Q : State→Prop}
 (h : WP isa c s Q) (ht : Tables s) (hn : c.aarch64Depth≤1) :
 WP isa c s fun t=>Q t ∧ Tables t := by
 obtain ⟨tr,t,he,hq⟩:=h
 exact ⟨tr,t,he,hq,ht.execDepth he hn⟩

theorem Tables.exec {s t : State} {c : Prog isa} {tr : List Leak}
 (h : Tables s) (he : Exec isa c s tr t) (hn : c.noFrames=true) : Tables t := by
 obtain ⟨hr,hw,hsp,hf⟩:=VG.AArch64.Exec.regions he hn
 exact h.frame (VG.AArch64.Exec.syms he) hr hw hsp hf

theorem WP.tables {s : State} {c : Prog isa} {Q : State→Prop}
 (h : WP isa c s Q) (ht : Tables s) (hn : c.noFrames=true) :
 WP isa c s fun t=>Q t ∧ Tables t := by
 obtain ⟨tr,t,he,hq⟩:=h
 exact ⟨tr,t,he,hq,ht.exec he hn⟩
end VG.Proof.MlKem.AArch64.Optimized
