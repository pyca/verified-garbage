import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit

/-! ## From `ResponseHintGroup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq wp_strq wp_vop)

def hintCt (s : State) (off e : Nat) : BitVec 32 :=
  reduceWord (vword (s.mem.read (s.gpr .x1+BitVec.ofNat 64 off) 16) e)
def hintInput (s : State) (off e : Nat) : BitVec 32 :=
  hintCt s off e+vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) e
def hintOutput (s : State) (off e : Nat) : BitVec 32 :=
  hintWord (vword (s.v .v17) e) (hintInput s off e)
    (vword (s.mem.read (s.gpr .x2+BitVec.ofNat 64 off) 16) e)
def hintHead (off : Nat) : List Instr :=
  [.ldrq .v0 .x1 off,.ldrq .v3 .x0 off,.ldrq .v4 .x2 off] ++
  Impl.MlDsa.AArch64.Optimized.Response.reduce .v0 ++
  Impl.MlDsa.AArch64.Optimized.Response.testNorm ++ [.vop (.add .s4 .v0 .v0 .v3)] ++ hintVector

theorem hintHead_ok {s : State} {off : Nat} (ho : off%16=0 ∧ off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hd : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v25) e=4194304#32)
    (hn : ∀e<4,vword (s.v .v18) e= -vword (s.v .v17) e)
    (hz : ∀e<4,vword (s.v .v23) e=0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v0,.v2,.v3,.v4,.v6,.v31] s t →
      (∀e<4,vword (t.v .v2) e=hintOutput s off e) →
      (∀e<4,vword (t.v .v31) e=vword (s.v .v31) e |||
        normMask (hintCt s off e) (vword (s.v .v27) e) (vword (s.v .v24) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (hintHead off++rest)) s Q := by
  unfold hintHead
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl hb fun a h1 => ?_
  refine wp_ldrq ho rfl (by simpa only [h1.chg.rd,h1.chg.wr,h1.chg.gpr] using ha) fun b h2 => ?_
  have hk : VChg [.v0,.v3] s b := (h1.chg.trans h2.chg).mono (by decide)
  refine wp_ldrq ho rfl (by simpa only [hk.rd,hk.wr,hk.gpr] using hd) fun c h3 => ?_
  have hk' : VChg [.v0,.v3,.v4] s c := (hk.trans h3.chg).mono (by decide)
  refine reduce_ok (by decide : VReg.v0≠.v6)
    (by intro e he; rw [hk'.get .v16 (by decide)]; exact hq e he)
    (by intro e he; rw [hk'.get .v25 (by decide)]; exact hc e he) fun d h4 hv => ?_
  have hct : ∀e<4,vword (d.v .v0) e=hintCt s off e := by
    intro e he
    rw [hv e he,h3.get .v0,h2.get .v0,h1.v]
    rfl
  have kd : VChg [.v0,.v3,.v4,.v6] s d := (hk'.trans h4).mono (by decide)
  refine norm_ok fun f h5 hnorm => ?_
  have kf : VChg [.v0,.v2,.v3,.v4,.v6,.v31] s f := (kd.trans h5).mono (by decide)
  refine wp_vop (d:=.v0) rfl fun g h6 => ?_
  have kg : VChg [.v0,.v2,.v3,.v4,.v6,.v31] s g := (kf.trans h6.chg).mono (by decide)
  refine hintVector_ok
    (by intro e he; rw [kg.get .v18 (by decide),kg.get .v17 (by decide)]; exact hn e he)
    (by intro e he; rw [kg.get .v23 (by decide)]; exact hz e he) fun t ht hv => ?_
  refine k t ((kg.trans ht).mono (by decide)) ?_ ?_
  · intro e he
    rw [hv e he,kg.get .v17 (by decide),h6.v,VG.AArch64.vword_map2 _ _ _ he,
      h5.get .v0 (by decide),hct e he,h5.get .v3 (by decide),h4.get .v3 (by decide),
      h3.get .v3,h2.v,h1.chg.gpr,h1.chg.mem,
      h6.get .v4 (by decide),h5.get .v4 (by decide),h4.get .v4 (by decide),h3.v,hk.mem,hk.gpr]
    rfl
  · intro e he
    rw [ht.get .v31 (by decide),h6.get .v31 (by decide),hnorm e he,hct e he,
      kd.get .v31 (by decide),kd.get .v27 (by decide),kd.get .v24 (by decide)]

def hintGroup (off : Nat) : List Instr := hintHead off ++
  [.strq .v2 .x0 off,.vop (.add .s4 .v30 .v30 .v2)]

theorem hintGroup_ok {s : State} {off : Nat} (ho : off%16=0 ∧ off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hd : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v25) e=4194304#32)
    (hn : ∀e<4,vword (s.v .v18) e= -vword (s.v .v17) e)
    (hz : ∀e<4,vword (s.v .v23) e=0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepKeep [.v0,.v2,.v3,.v4,.v6,.v30,.v31] s t →
      t.mem=s.mem.write (s.gpr .x0+BitVec.ofNat 64 off) 16 (laneVector (hintOutput s off)) →
      (∀e<4,vword (t.v .v30) e=vword (s.v .v30) e+hintOutput s off e) →
      (∀e<4,vword (t.v .v31) e=vword (s.v .v31) e |||
        normMask (hintCt s off e) (vword (s.v .v27) e) (vword (s.v .v24) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (hintGroup off++rest)) s Q := by
  unfold hintGroup
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine hintHead_ok ho ha hb hd hq hc hn hz fun a hk hv hm => ?_
  have vv : a.v .v2=laneVector (hintOutput s off) := by
    apply vec_ext; intro e he; rw [laneVector_word _ he,hv e he]
  refine wp_strq ho rfl (by simpa only [hk.wr,hk.gpr] using hw) fun b hb => ?_
  refine wp_vop (d:=.v30) rfl fun t ht => ?_
  refine k t ?_ ?_ ?_ ?_
  · exact (((StepKeep.ofChg hk (by decide)).trans (StepKeep.ofMem hb)).trans
      (StepKeep.ofChg ht.chg (by decide))).mono (by decide)
  · rw [ht.chg.mem,hb.mem,hk.mem,hk.gpr,vv]
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.v,hk.get .v30 (by decide),hv e he]
  · intro e he
    rw [ht.get .v31 (by decide),hb.v,hm e he]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseHintInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)

structure HintReady (B : BitVec 32) (s : State) : Prop extends ZReady B s where
  gamma : ∀e<4,vword (s.v .v17) e=B
  negGamma : ∀e<4,vword (s.v .v18) e= -B
  zero : ∀e<4,vword (s.v .v23) e=0

theorem HintReady.frame {B : BitVec 32} {s t : State} {rs : List VReg}
    (h : HintReady B s) (hf : ∀r,r∉rs → t.v r=s.v r)
    (hv : ∀r∈[VReg.v16,.v25,.v27,.v24,.v17,.v18,.v23],r∉rs) : HintReady B t := by
  constructor
  · exact h.toZReady.frame (by intro r hr; exact hv r ((by decide : ∀r∈[VReg.v16,.v25,.v27,.v24],r∈[VReg.v16,.v25,.v27,.v24,.v17,.v18,.v23]) r hr)) hf
  · intro e he; rw [hf .v17 (hv _ (by decide))]; exact h.gamma e he
  · intro e he; rw [hf .v18 (hv _ (by decide))]; exact h.negGamma e he
  · intro e he; rw [hf .v23 (hv _ (by decide))]; exact h.zero e he

def hintInit : List Instr :=
  Impl.MlDsa.AArch64.Optimized.HighPack.vc .v16 8380417 ++
  Impl.MlDsa.AArch64.Optimized.HighPack.vc .v25 4194304 ++
  [.vop (.dup .s4 .v24 .x3),.vop (.dup .s4 .v17 .x3),
   .vop (.movi0 .v23),.vop (.sub .s4 .v18 .v23 .v17),
   .vop (.movi0 .v30),.vop (.movi0 .v31)] ++
  Impl.MlDsa.AArch64.Optimized.Response.normConstants

theorem hintInit_ok (s : State) : WP isa (.block hintInit) s fun t =>
    SetupKeep [.v16,.v25,.v24,.v17,.v18,.v23,.v30,.v31,.v27] s t ∧
    HintReady ((s.gpr .x3).setWidth 32) t ∧ t.v .v30=0 ∧ t.v .v31=0 := by
  unfold hintInit
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s .v16 8380417) fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok a .v25 4194304) fun b hb => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d:=.v24) rfl fun c hc => wp_vop (d:=.v17) rfl fun d hd =>
    wp_vop (d:=.v23) rfl fun f hf => wp_vop (d:=.v18) rfl fun g hg =>
    wp_vop (d:=.v30) rfl fun h hh => wp_vop (d:=.v31) rfl fun i hi => ?_
  have hs : SetupKeep [.v16,.v25,.v24,.v17,.v18,.v23,.v30,.v31] s i := setup_mono
    (((SetupKeep.ofConst ha.1).trans (SetupKeep.ofConst hb.1)).trans
      (setup_ofChg (((((hc.chg.trans hd.chg).trans hf.chg).trans hg.chg).trans hh.chg).trans hi.chg))) (by decide)
  have dup_lane (e : Nat) (he : e<4) :
      vword (ofVWords ((s.gpr .x3).setWidth 32) ((s.gpr .x3).setWidth 32)
        ((s.gpr .x3).setWidth 32) ((s.gpr .x3).setWidth 32)) e=(s.gpr .x3).setWidth 32 := by
    rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
    have heq : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
    rcases heq with rfl | rfl | rfl | rfl <;> rfl
  have h24 : ∀e<4,vword (i.v .v24) e=(s.gpr .x3).setWidth 32 := by
    intro e he
    rw [hi.get .v24 (by decide),hh.get .v24 (by decide),hg.get .v24 (by decide),
      hf.get .v24 (by decide),hd.get .v24 (by decide),hc.v,
      hb.1.gpr .x3 (by decide),ha.1.gpr .x3 (by decide),dup_lane e he]
  have h17 : ∀e<4,vword (i.v .v17) e=(s.gpr .x3).setWidth 32 := by
    intro e he
    rw [hi.get .v17 (by decide),hh.get .v17 (by decide),hg.get .v17 (by decide),
      hf.get .v17 (by decide),hd.v,hc.chg.gpr,
      hb.1.gpr .x3 (by decide),ha.1.gpr .x3 (by decide),dup_lane e he]
  have h18 : ∀e<4,vword (i.v .v18) e= -(s.gpr .x3).setWidth 32 := by
    intro e he
    rw [hi.get .v18 (by decide),hh.get .v18 (by decide),hg.v,VG.AArch64.vword_map2 _ _ _ he,hf.v]
    have h := h17 e he
    rw [hi.get .v17 (by decide),hh.get .v17 (by decide),hg.get .v17 (by decide)] at h
    rw [h]
    simp [vword]
  refine WP.mono (normConstants_ok i) fun t ⟨ht,hlo,hw⟩ => ?_
  refine ⟨setup_mono (hs.trans ht) (by decide),⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩,?_,?_⟩
  · intro e he
    rw [ht.vec .v16 (by decide),hi.get .v16 (by decide),hh.get .v16 (by decide),hg.get .v16 (by decide),
      hf.get .v16 (by decide),hd.get .v16 (by decide),hc.get .v16 (by decide),
      hb.1.vec .v16 (by decide),ha.2,HighPack.repeatedWord_lane _ he]
  · intro e he
    rw [ht.vec .v25 (by decide),hi.get .v25 (by decide),hh.get .v25 (by decide),hg.get .v25 (by decide),
      hf.get .v25 (by decide),hd.get .v25 (by decide),hc.get .v25 (by decide),hb.2,HighPack.repeatedWord_lane _ he]
  · intro e he; rw [hlo e he,h24 e he]
  · intro e he; rw [hw e he,h24 e he]
  · intro e he; rw [ht.vec .v17 (by decide),h17 e he]
  · intro e he; rw [ht.vec .v18 (by decide),h18 e he]
  · intro e he
    rw [ht.vec .v23 (by decide),hi.get .v23 (by decide),hh.get .v23 (by decide),hg.get .v23 (by decide),hf.v]
    simp [vword]
  · rw [ht.vec .v30 (by decide),hi.get .v30 (by decide),hh.v]
  · rw [ht.vec .v31 (by decide),hi.v]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

/-! ## From `ResponseHintMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

structure HintData where
  mem : Mem
  counts : BitVec 128
  flags : BitVec 128

def hintCtAt (m : Mem) (a : Addr) (j e : Nat) : BitVec 32 :=
  reduceWord (vword (m.read (a+BitVec.ofNat 64 (16*j)) 16) e)
def hintAt (B : BitVec 32) (m : Mem) (p a h : Addr) (j e : Nat) : BitVec 32 :=
  hintWord B (hintCtAt m a j e+vword (m.read (p+BitVec.ofNat 64 (16*j)) 16) e)
    (vword (m.read (h+BitVec.ofNat 64 (16*j)) 16) e)
def hintStep (B : BitVec 32) (p a h : Addr) (j : Nat) (d : HintData) : HintData :=
  { mem := d.mem.write (p+BitVec.ofNat 64 (16*j)) 16 (laneVector (hintAt B d.mem p a h j))
    counts := laneVector fun e => vword d.counts e+hintAt B d.mem p a h j e
    flags := laneVector fun e => vword d.flags e ||| normMask (hintCtAt d.mem a j e) (B-1) (B+(B-1)) }
def hintRun (m : Mem) (B : BitVec 32) (p a h : Addr) : Nat → HintData
  | 0 => ⟨m,0,0⟩
  | j+1 => hintStep B p a h j (hintRun m B p a h j)

theorem hintGroup_step {B : BitVec 32} {s : State} {d : HintData} {p a h : Addr} {u i : Nat}
    (hi : i<4) (hr : HintReady B s) (hm : s.mem=d.mem)
    (hf : s.v .v31=d.flags) (hc : s.v .v30=d.counts)
    (h0 : s.gpr .x0=p+BitVec.ofNat 64 (64*u)) (h1 : s.gpr .x1=a+BitVec.ofNat 64 (64*u))
    (h2 : s.gpr .x2=h+BitVec.ofNat 64 (64*u))
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hd : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (16*i)) 16)
    (hw : InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (hintGroup (16*i))) s fun t =>
      StepKeep [.v0,.v2,.v3,.v4,.v6,.v30,.v31] s t ∧ HintReady B t ∧
      t.mem=(hintStep B p a h (4*u+i) d).mem ∧
      t.v .v31=(hintStep B p a h (4*u+i) d).flags ∧
      t.v .v30=(hintStep B p a h (4*u+i) d).counts := by
  have addr (r : Reg) (q : Addr) (hv : s.gpr r=q+BitVec.ofNat 64 (64*u)) :
      s.gpr r+BitVec.ofNat 64 (16*i)=q+BitVec.ofNat 64 (16*(4*u+i)) := by
    rw [hv,BitVec.add_assoc,← BitVec.ofNat_add,show 64*u+16*i=16*(4*u+i) by omega]
  have hct : hintCt s (16*i)=hintCtAt d.mem a (4*u+i) := by
    funext e; simp only [hintCt,hintCtAt,hm,addr _ _ h1]
  have hout : ∀e<4,hintOutput s (16*i) e=hintAt B d.mem p a h (4*u+i) e := by
    intro e he
    simp only [hintOutput,hintInput,hintAt,hct,hm,addr _ _ h0,addr _ _ h2,hr.gamma e he]
  have houtv : laneVector (hintOutput s (16*i))=laneVector (hintAt B d.mem p a h (4*u+i)) := by
    apply vec_ext; intro e he
    rw [laneVector_word _ he,laneVector_word _ he,hout e he]
  rw [←List.append_nil (hintGroup (16*i))]
  refine hintGroup_ok (by omega) ha hb hd hw hr.q hr.c
    (by intro e he; rw [hr.negGamma e he,hr.gamma e he]) hr.zero
    fun t hk hmem hcount hflag => WP.block_nil_iff.mpr ?_
  refine ⟨hk,hr.frame hk.vec (by decide),?_,?_,?_⟩
  · simpa only [hintStep,hm,addr _ _ h0,houtv] using hmem
  · apply vec_ext; intro e he
    rw [hflag e he,hct,hr.lo e he,hr.width e he,hf]
    dsimp only [hintStep]
    rw [laneVector_word _ he]
  · apply vec_ext; intro e he
    rw [hcount e he,hout e he,hc]
    dsimp only [hintStep]
    rw [laneVector_word _ he]

end VG.Proof.MlDsa.AArch64.Optimized.Response

end
