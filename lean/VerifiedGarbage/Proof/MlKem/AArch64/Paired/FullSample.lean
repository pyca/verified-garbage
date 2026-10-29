module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SeedSpec
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullReject
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullInit
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SingleStep
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Squeeze

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdSplit
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Single
/-! # The complete singleton fallback, including parser failure and saved flags -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/FullPrepare.lean`, which only this module imported.
section

/-! # Constants and complete-stream rejection entry for the singleton fallback -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64

def fullPrep (out : Nat) : List Instr := Rej8.rejConsts ++
  [.movz .x .x9 0 0,.str .x .x9 .x19 1240] ++ fullEntry 400 out

def prepWrites (p : Addr) : List Region := [⟨p+1408,8⟩,⟨p+1240,8⟩]
def prepRegs : List Reg := [.x2,.x3,.x4,.x5,.x9,.x10,.x16]

theorem fullPrep_ok {w16 : Bool} {s : State} {p out : Addr} {off : Nat} {B : Nat → Byte}
    (hoff : off<65536) (hp : s.gpr .x19=p) (hout : s.gpr .x28+BitVec.ofNat 64 off=out)
    (hc : Covers [⟨p,2048⟩] s.wr) (ho : Covers [⟨out,1024⟩] s.wr)
    (hd : (Region.mk p 2048).Disjoint ⟨out,1024⟩)
    (bytes : ∀i<840,s.mem ((p+400)+BitVec.ofNat 64 i)=B i)
    (tab : Rej8.TableArtifact s.mem (s.syms "VG_MLKEM_REJ_SHUFFLE"))
    (tr : Covers [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩] (s.rd++s.wr))
    (ts : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨p,2048⟩)
    (to : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨out,1024⟩) :
    WP isa (.block (fullPrep off)) s fun u =>
      Keep prepRegs s u ∧ Frame (prepWrites p) s.mem u.mem ∧ Rej8.EntryW w16 [] 280 B (p+400) out u ∧ u.gpr .x16=s.syms "VG_MLKEM_REJ_SHUFFLE" := by
  have iw {o l : Nat} (h : o+l≤2048) := Noise.inScratch hc h (by decide)
  rw [fullPrep,List.append_assoc,WP.block_append_iff]
  refine WP.mono_syms (Rej8.constants_ok s (by rw [hp]; exact iw (by decide))) fun a ⟨ka,ca,ma,ta⟩ sa => ?_
  have fa : Frame (prepWrites p) s.mem a.mem := by
    rw [ma,hp]
    exact (Frame.refl _ _).writeW (r := ⟨p+1408,8⟩) (by simp [prepWrites]) _ (Region.contains_self _ 8)
  have zero : WP isa (.block [.movz .x .x9 0 0,.str .x .x9 .x19 1240]) a fun c =>
      Keep [.x9] a c ∧ c.mem=a.mem.writeW (p+1240) (0 : BitVec 64) := by
    refine wp_movz fun b kb eb => wp_strx (a := p+1240) (by decide)
      (by rw [kb.get .x19,ka.get .x19,hp]; rfl)
      (by rw [kb.wr,ka.wr]; exact iw (by decide)) fun c kc => wp_nil ?_
    exact ⟨(kb.keep.trans kc.keep).mono (by decide),by rw [kc.mem,eb,kb.mem]; rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepV (by decide) zero) fun c ⟨⟨kc,mc⟩,vc⟩ => ?_
  have pc : Keep [.x9,.x16] s c := (ka.trans kc).mono (by decide)
  have fc : Frame (prepWrites p) s.mem c.mem := by
    rw [mc]; exact fa.writeW (r := ⟨p+1240,8⟩) (by simp [prepWrites]) _ (Region.contains_self _ 8)
  have subs : ∀r∈prepWrites p,Region.Sub r ⟨p,2048⟩ := by
    intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base p (by decide)
  have cc : Rej8.Constants c := by
    have v : c.v=a.v := vc
    exact ⟨by rw [v]; exact ca.index,by rw [v]; exact ca.mask,
      by simpa only [v] using ca.q,by simpa only [v] using ca.weights,by simpa only [v] using ca.zero⟩
  have c16 : c.gpr .x16=s.syms "VG_MLKEM_REJ_SHUFFLE" := by rw [kc.get .x16,ta,sa]
  have ready : Rej8.TableReady c out := by
    refine ⟨?_,?_,?_⟩
    · rw [c16]; exact tab.frame fc (fun r hr => ts.sub_right (subs r hr))
    · rw [c16,pc.rd,pc.wr]; exact tr
    · rw [c16]; exact to
  have env : Rej8.EnvW w16 280 B (p+400) out c := rejection_envW (w16 := w16) (by decide) (by decide)
    (by rw [pc.wr]; exact hc) (by rw [pc.wr]; exact ho) hd
    (by
      intro i hi
      have hsep : ∀r∈prepWrites p,(Region.mk (p+400) 840).Disjoint r := by
        intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint p (by decide) (by decide) (by decide)
      exact (fc.bytes hsep (by change 840≤2^64; decide) hi).trans (bytes i hi))
    (fun _ hm => ready.read hm) (fun _ hm => ready.artifact.vector hm) (fun _ hm => ready.disjoint hm)
  have env' : Rej8.EnvW w16 280 B (c.gpr .x19+400) (c.gpr .x28+BitVec.ofNat 64 off) c := by
    rw [pc.get .x19,pc.get .x28,hp,hout]; exact env
  refine WP.mono (fullEntry_ok c (by decide) hoff env' cc) fun u ⟨ku,eu⟩ => ?_
  refine ⟨(pc.trans ku.keep).mono (by decide),?_,?_,(ku.get .x16).trans c16⟩
  · rw [ku.mem]; exact fc
  · rw [pc.get .x19,pc.get .x28,hp,hout] at eu
    exact eu

end VG.Proof.MlKem.AArch64.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/FullStart.lean`, which only this module imported.
section

/-! # Singleton fallback through all five SHAKE128 blocks -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3 (iterF)

def fullStartRegs : List Reg := initRegs++singleRegs

theorem fullStart_ok {s initial : State} {p seed : Addr} {sb ss a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0)
    (hp : s.gpr .x19=p) (hbase : s.gpr .x28+BitVec.ofNat 64 ss=p)
    (hseed : s.gpr .x28+BitVec.ofNat 64 sb=seed)
    (hin : ∀j<4, InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hc : Covers [⟨p,2048⟩] s.wr) (hsep : (Region.mk seed 32).Disjoint ⟨p,2048⟩)
    (sv : Noise.Saved p initial s.mem) :
    WP isa (.seq (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k))
      (.loop singleBody (.nonzero .x .x22))) s fun t =>
      Keep fullStartRegs s t ∧ Frame [⟨p,2048⟩] s.mem t.mem ∧ Noise.Saved p initial t.mem ∧ Flags p s t.mem ∧
      t.gpr .x19=p ∧ t.gpr .x22=0 ∧
      PairAt t.mem p (iterF 5 (seedState s.mem seed a k)) (iterF 5 (seedState s.mem seed a k)) ∧
      Blocks t.mem (p+400) 5 (seedState s.mem seed a k) := by
  have iw {o l : Nat} (h : o+l≤2048) := Noise.inScratch hc h (by decide)
  refine WP.seq (WP.mono (fullInit_ok hss hsb h8 hp hbase hseed hin hc hsep)
    fun u ⟨ku,fu,flags,h19,h20,_,h22,pair⟩ => ?_)
  have svu : Noise.Saved p initial u.mem := sv.frame fu (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint_base p (by decide) (by decide))
  refine WP.mono (single_ok h19 h20 (by rw [h22]; rfl) pair
    (fun i hi => by
      rw [ku.rd,ku.wr]; obtain ⟨r,hr,hh⟩ := iw (by omega : 16*i+8≤2048)
      exact ⟨r,List.mem_append_right _ hr,hh⟩)
    (fun j hj i hi => by
      rw [ku.wr]; change InRegions s.wr ((p+BitVec.ofNat 64 400+BitVec.ofNat 64 (168*j))+BitVec.ofNat 64 (8*i)) 8
      rw [BitVec.add_assoc,BitVec.add_assoc,← BitVec.ofNat_add,← BitVec.ofNat_add]
      exact iw (by omega))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.disjoint p (by decide) (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (by
      rw [ku.wr]
      have ha : Covers [pairR p] s.wr := by
        simpa only [BitVec.add_zero,pairR] using (Noise.coversScratch (off := 0) (len := 400) hc (by decide))
      exact Noise.coversTwo ha (Noise.coversScratch (off := 1536) (len := 136) hc (by decide)))) fun t ht => ?_
  refine ⟨ku.trans ht.keep,?_,?_,?_,ht.ptr,?_,ht.pair,ht.out⟩
  · have fi : Frame [⟨p,2048⟩] s.mem u.mem := fu.sub (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩
      · exact ⟨⟨p,2048⟩,by simp,Region.sub_prefix (by decide : 400≤2048)⟩)
    exact fi.trans (ht.frame.sub (by
      intro r hr; simp only [singleWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨p,2048⟩,by simp,Region.sub_prefix (by decide : 400≤2048)⟩
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩))
  · apply svu.frame ht.frame
    intro r hr; simp only [singleWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
  · apply flags.frame ht.frame
    intro r hr; simp only [singleWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
  · apply BitVec.eq_of_toNat_eq; exact ht.count

end VG.Proof.MlKem.AArch64.Paired
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem VG.Spec.MlKem

def fullSampleCode (sb ss off a k : Nat) (w16 : Bool := false) : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k))
    (.seq (.loop singleBody (.nonzero .x .x22)) (.seq (.block (fullPrep off)) (fullFinish w16)))

theorem fullSample_eq (L : KemLay) (kg : Bool) (a : Nat) (w16 : Bool) :
    Impl.MlKem.AArch64.Paired.fullSample L kg a w16 =
      fullSampleCode (if kg then KG.SB else KEM.SB) (if kg then KG.SS else KEM.SS)
        ((if kg then KG.AH else KEM.AH)+1024*a) a L.k w16 := by
  simp only [Impl.MlKem.AArch64.Paired.fullSample,fullSampleCode,fullPrep,fullEntry,
    fullFinish,singleBody,singleWords,Rej8.zeroSuffix,Rej8.zeroBody,seqs,List.append_assoc]

def fullRegs : List Reg := fullStartRegs++prepRegs++fullFinishRegs

def fullWrites (p out : Addr) : List Region := [⟨p,2048⟩,polyRegion out]

structure FullPostW (w16 : Bool) (B : Nat → Byte) (p out : Addr) (initial s u : State) : Prop where
  keep : Keep fullRegs s u
  frame : Frame (fullWrites p out) s.mem u.mem
  saved : Noise.Saved p initial u.mem
  coeffs : CoeffsUpToW w16 u.mem out (sampleAfter [] B 280).length (Sample.cvW w16 (sampleAfter [] B 280)) (fun _ => 0)
  reduced : ReducedW (cw w16) u.mem out
  status : u.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleAfter [] B 280).length=256 then 1 else 0)
  flag22 : u.gpr .x22=s.gpr .x22
  flag23 : u.gpr .x23=s.gpr .x23
  ptr : u.gpr .x19=p

theorem fullSampleCode_ok {w16 : Bool} {s initial : State} {p seed out : Addr} {sb ss off a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (hp : s.gpr .x19=p) (hbase : s.gpr .x28+BitVec.ofNat 64 ss=p)
    (hseed : s.gpr .x28+BitVec.ofNat 64 sb=seed) (hout : s.gpr .x28+BitVec.ofNat 64 off=out)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hc : Covers [⟨p,2048⟩] s.wr) (ho : Covers [⟨out,1024⟩] s.wr)
    (hsep : (Region.mk seed 32).Disjoint ⟨p,2048⟩)
    (hd : (Region.mk p 2048).Disjoint ⟨out,1024⟩)
    (sv : Noise.Saved p initial s.mem)
    (tab : Rej8.TableArtifact s.mem (s.syms "VG_MLKEM_REJ_SHUFFLE"))
    (tr : Covers [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩] (s.rd++s.wr))
    (ts : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨p,2048⟩)
    (to : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨out,1024⟩) :
    WP isa (fullSampleCode sb ss off a k w16) s
      (FullPostW w16 (xofByte (seedBytes s.mem seed a k)) p out initial s) := by
  have combined := WP.mono_syms (fullStart_ok (a := a) (k := k) hss hsb h8 hp hbase hseed hin hc hsep sv)
    (R := fun b => WP isa (.seq (.block (fullPrep off)) (fullFinish w16)) b
      (FullPostW w16 (xofByte (seedBytes s.mem seed a k)) p out initial s))
    (fun b ⟨kb,fb,svb,flagsb,b19,_,_,blocks⟩ sy => by
      refine WP.seq (WP.mono (fullPrep_ok (w16 := w16) hoff b19
        (by rw [kb.get .x28]; exact hout) (by rw [kb.wr]; exact hc) (by rw [kb.wr]; exact ho) hd
        (fun i hi => blocks.xof hk hk256 hi)
        (by rw [sy]; exact tab.frame fb (by simpa using ts))
        (by rw [sy,kb.rd,kb.wr]; exact tr) (by rw [sy]; exact ts) (by rw [sy]; exact to)) fun c ⟨kc,fc,entry,_⟩ => ?_)
      have prepSub : ∀r∈prepWrites p,Region.Sub r ⟨p,2048⟩ := by
        intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.sub_base p (by decide)
      have prepFlag : ∀r∈prepWrites p,(flagR p).Disjoint r := by
        intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint p (by decide) (by decide) (by decide)
      have prepSaved : ∀r∈prepWrites p,(Noise.savedR p).Disjoint r := by
        intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint p (by decide) (by decide) (by decide)
      have cf := flagsb.frame fc prepFlag
      have cs := svb.frame fc prepSaved
      have flagOut : (flagR p).Disjoint (polyRegion out) :=
        hd.sub_left (Offset.sub_base p (by decide))
      have savedOut : (Noise.savedR p).Disjoint (polyRegion out) :=
        hd.sub_left (Offset.sub_base p (by decide))
      have read {off : Nat} (fit : off+8≤2048) : InRegions (c.rd++c.wr) (p+BitVec.ofNat 64 off) 8 := by
        rw [kc.rd,kc.wr,kb.rd,kb.wr]
        obtain ⟨r,hr,hh⟩ := Noise.inScratch hc fit (by decide)
        exact ⟨r,List.mem_append_right _ hr,hh⟩
      refine WP.mono (fullFinish_ok entry (by rw [kc.get .x19,b19]) cf flagOut
        (read (by decide)) (read (by decide))) fun u hu => ?_
      refine ⟨?_,?_,cs.frame hu.frame (by simpa using savedOut),hu.coeffs,hu.reduced,?_,hu.flag22,hu.flag23,?_⟩
      · exact ((kb.trans kc).trans hu.keep).mono (by simp [fullRegs,List.append_assoc])
      · have first : Frame (fullWrites p out) s.mem b.mem := fb.mono (by simp [fullWrites])
        have second : Frame (fullWrites p out) b.mem c.mem := fc.sub (fun r hr =>
          ⟨⟨p,2048⟩,by simp [fullWrites],prepSub r hr⟩)
        exact (first.trans second).trans (hu.frame.mono (by simp [fullWrites]))
      · rw [hu.status,kc.get .x24,kb.get .x24]
      · rw [hu.keep.get .x19,kc.get .x19,b19])
  exact WP.seq (WP.mono (WP.seq_iff.mp combined) fun b hb => WP.seq hb)

end VG.Proof.MlKem.AArch64.Paired
