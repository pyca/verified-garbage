import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintGroup

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
