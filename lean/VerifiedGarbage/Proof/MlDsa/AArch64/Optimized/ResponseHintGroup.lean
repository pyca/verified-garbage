import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd

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
