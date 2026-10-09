import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq wp_strq wp_vop)
open VG.Proof.MlDsa.AArch64.Round (IsG)

def subInput (s : State) (off e : Nat) : BitVec 32 :=
  Inverse.signCorrected (reduceWord (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 off) 16) e-
    vword (s.mem.read (s.gpr .x1+BitVec.ofNat 64 off) 16) e))
def subHead (g off : Nat) : List Instr :=
  [.ldrq .v0 .x0 off,.ldrq .v1 .x1 off,.vop (.sub .s4 .v0 .v0 .v1)] ++
    Impl.MlDsa.AArch64.Optimized.Response.reduce .v0 ++
    Impl.MlDsa.AArch64.Optimized.Response.cadd .v0 ++
    Impl.MlDsa.AArch64.Optimized.HighPack.hb g .v1 .v0

theorem subHead_ok {g : Nat} (hg : IsG g) {s : State} {off : Nat}
    (ho : off%16=0 ∧ off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v25) e=4194304#32) (hh : HighPack.HighConstants g s)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v0,.v1,.v6,.v7] s t →
      (∀e<4,vword (t.v .v0) e=subInput s off e) →
      (∀e<4,vword (t.v .v1) e=HighPack.highWord g (subInput s off e)) →
      WP isa (.block rest) t Q) : WP isa (.block (subHead g off++rest)) s Q := by
  unfold subHead
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl ha fun a h1 => ?_
  refine wp_ldrq ho rfl (by simpa only [h1.chg.rd,h1.chg.wr,h1.chg.gpr] using hb) fun b h2 => ?_
  refine wp_vop (d:=.v0) rfl fun c h3 => ?_
  have hk : VChg [.v0,.v1] s c := ((h1.chg.trans h2.chg).trans h3.chg).mono (by decide)
  refine reduce_ok (by decide : VReg.v0≠.v6)
    (by intro e he; rw [hk.get .v16 (by decide)]; exact hq e he)
    (by intro e he; rw [hk.get .v25 (by decide)]; exact hc e he) fun d hd hv => ?_
  have hd' : VChg [.v0,.v1,.v6] s d := (hk.trans hd).mono (by decide)
  refine cadd_ok (by decide : VReg.v0≠.v7)
    (by intro e he; rw [hd'.get .v16 (by decide)]; exact hq e he) fun u hu huv => ?_
  have hu' : VChg [.v0,.v1,.v6,.v7] s u := (hd'.trans hu).mono (by decide)
  have hval : ∀e<4,vword (u.v .v0) e=subInput s off e := by
    intro e he
    rw [huv e he,hv e he,h3.v,VG.AArch64.vword_map2 _ _ _ he,
      h2.get .v0,h1.v,h2.v,h1.chg.mem,h1.chg.gpr]
    rfl
  have cu := hh.chg hu' (by decide) (by decide) (by decide) (by decide)
  refine HighPack.hb_ok hg (by decide : VReg.v1≠.v7) (by decide) (by decide) (by decide)
    cu.add cu.mul cu.round cu.modulus fun t ht hw => ?_
  exact k t ((hu'.trans ht).mono (by decide))
    (fun e he => by rw [ht.get .v0 (by decide)]; exact hval e he)
    (fun e he => by rw [hw e he,hval e he])

def subGroup (g off : Nat) : List Instr := subHead g off ++ [.strq .v1 .x0 off] ++
  lowCorrection ++ [.strq .v0 .x2 off] ++ Impl.MlDsa.AArch64.Optimized.Response.testNorm

def subLow (g : Nat) (s : State) (off e : Nat) : BitVec 32 :=
  lowWord (subInput s off e) (HighPack.highWord g (subInput s off e)) (vword (s.v .v21) e)

theorem subGroup_ok {g : Nat} (hg : IsG g) {s : State} {off : Nat}
    (ho : off%16=0 ∧ off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hl : InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v25) e=4194304#32)
    (hh : ∀e<4,vword (s.v .v26) e=4190208#32) (hr : HighPack.HighConstants g s)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepKeep [.v0,.v1,.v2,.v6,.v7,.v31] s t →
      t.mem=(s.mem.write (s.gpr .x0+BitVec.ofNat 64 off) 16
        (laneVector (fun e => HighPack.highWord g (subInput s off e)))).write
          (s.gpr .x2+BitVec.ofNat 64 off) 16 (laneVector (subLow g s off)) →
      (∀e<4,vword (t.v .v31) e=vword (s.v .v31) e |||
        normMask (subLow g s off e) (vword (s.v .v27) e) (vword (s.v .v24) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (subGroup g off++rest)) s Q := by
  unfold subGroup
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine subHead_ok hg ho ha hb hq hc hr fun a ha h0 h1 => ?_
  refine wp_strq ho rfl (by simpa only [ha.wr,ha.gpr] using hw) fun b hb => ?_
  refine lowCorrection_ok
    (by intro e he; rw [hb.v,ha.get .v16 (by decide)]; exact hq e he)
    (by intro e he; rw [hb.v,ha.get .v26 (by decide)]; exact hh e he) fun c hc hv => ?_
  have hk : StepKeep [.v0,.v1,.v6,.v7] s c :=
    (((StepKeep.ofChg ha (by decide)).trans (StepKeep.ofMem hb)).trans
      (StepKeep.ofChg hc (by decide))).mono (by decide)
  have vl : c.v .v0=laneVector (subLow g s off) := by
    apply vec_ext; intro e he
    rw [laneVector_word _ he,hv e he,hb.v,h0 e he,h1 e he,ha.get .v21 (by decide)]
    rfl
  have vh : a.v .v1=laneVector (fun e => HighPack.highWord g (subInput s off e)) := by
    apply vec_ext; intro e he; rw [laneVector_word _ he,h1 e he]
  refine wp_strq ho rfl (by simpa only [hk.keep.wr,hk.keep.get .x2] using hl) fun d hd => ?_
  refine norm_ok fun t ht hn => ?_
  refine k t ?_ ?_ ?_
  · exact ((hk.trans (StepKeep.ofMem hd)).trans (StepKeep.ofChg ht (by decide))).mono (by decide)
  · rw [ht.mem,hd.mem,hk.keep.get .x2,vl,hc.mem,hb.mem,ha.mem,ha.gpr,vh]
  · intro e he
    rw [hn e he,hd.v,vl,laneVector_word _ he,hk.vec .v31 (by decide),hk.vec .v27 (by decide),hk.vec .v24 (by decide)]

end VG.Proof.MlDsa.AArch64.Optimized.Response
