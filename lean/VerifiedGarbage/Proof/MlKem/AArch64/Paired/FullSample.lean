module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullPrepare
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output

/-! # The complete singleton fallback, including parser failure and saved flags -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem VG.Spec.MlKem

def fullSampleCode (sb ss off a k : Nat) : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k))
    (.seq (.loop singleBody (.nonzero .x .x22)) (.seq (.block (fullPrep off)) fullFinish))

theorem fullSample_eq (L : KemLay) (kg : Bool) (a : Nat) :
    Impl.MlKem.AArch64.Paired.fullSample L kg a =
      fullSampleCode (if kg then KG.SB else KEM.SB) (if kg then KG.SS else KEM.SS)
        ((if kg then KG.AH else KEM.AH)+1024*a) a L.k := by
  simp only [Impl.MlKem.AArch64.Paired.fullSample,fullSampleCode,fullPrep,fullEntry,
    fullFinish,singleBody,singleWords,Rej8.zeroSuffix,Rej8.zeroBody,seqs,List.append_assoc,
    Bool.false_eq_true,ite_false]

def fullRegs : List Reg := fullStartRegs++prepRegs++fullFinishRegs

def fullWrites (p out : Addr) : List Region := [⟨p,2048⟩,polyRegion out]

structure FullPost (B : Nat → Byte) (p out : Addr) (initial s u : State) : Prop where
  keep : Keep fullRegs s u
  frame : Frame (fullWrites p out) s.mem u.mem
  saved : Noise.Saved p initial u.mem
  coeffs : CoeffsUpTo u.mem out (sampleAfter [] B 280).length (Sample.cv (sampleAfter [] B 280)) (fun _ => 0)
  reduced : Reduced u.mem out
  status : u.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleAfter [] B 280).length=256 then 1 else 0)
  flag22 : u.gpr .x22=s.gpr .x22
  flag23 : u.gpr .x23=s.gpr .x23
  ptr : u.gpr .x19=p

theorem fullSampleCode_ok {s initial : State} {p seed out : Addr} {sb ss off a k : Nat}
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
    WP isa (fullSampleCode sb ss off a k) s
      (FullPost (xofByte (seedBytes s.mem seed a k)) p out initial s) := by
  have combined := WP.mono_syms (fullStart_ok (a := a) (k := k) hss hsb h8 hp hbase hseed hin hc hsep sv)
    (R := fun b => WP isa (.seq (.block (fullPrep off)) fullFinish) b
      (FullPost (xofByte (seedBytes s.mem seed a k)) p out initial s))
    (fun b ⟨kb,fb,svb,flagsb,b19,_,_,blocks⟩ sy => by
      refine WP.seq (WP.mono (fullPrep_ok hoff b19
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
