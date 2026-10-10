import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

/-! ## From `BoundedFourInitMiddle.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def middleSetup : List Instr :=
 [.vop (.dup .b16 .v23 .x11),.vop (.dup .s4 .v22 .x15),.vop (.dup .s4 .v21 .x9),
 .vop (.dup .s4 .v20 .x10),.vop (.add .s4 .v20 .v20 .v21),.movz .x .x6 13 0,
 .vop (.dup .s4 .v18 .x6),.movz .x .x6 5 0,.vop (.dup .s4 .v19 .x6)]

def initWord (x : BitVec 32) : BitVec 128 := ofVWords x x x x

structure MiddleConstants (η : Nat) (s : State) : Prop where
 nibble : s.v .v23=ofVBytes (fun _=>15)
 bound : s.v .v22=initWord (BitVec.ofNat 32 (VG.Proof.MlDsa.Sample.rbB η))
 q : s.v .v21=initWord 8380417
 etaQ : s.v .v20=initWord (BitVec.ofNat 32 (Spec.MlDsa.q+η))
 thirteen : s.v .v18=initWord 13
 five : s.v .v19=initWord 5

theorem middleSetup_ok {s : State} {η : Nat} (he : η=2∨η=4)
    (h9 : s.gpr .x9=BitVec.ofNat 64 Spec.MlDsa.q)
    (h10 : s.gpr .x10=BitVec.ofNat 64 η) (h11 : s.gpr .x11=15)
    (h15 : s.gpr .x15=BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.rbB η)) :
    WP isa (.block middleSetup) s fun t=>
      InitKeep [.x6] [.v23,.v22,.v21,.v20,.v18,.v19] s t ∧ MiddleConstants η t := by
  unfold middleSetup
  refine wp_vop (d := .v23) rfl fun a ha=>wp_vop (d := .v22) rfl fun b hb=>
    wp_vop (d := .v21) rfl fun c hc=>wp_vop (d := .v20) rfl fun d hd=>
    wp_vop (d := .v20) rfl fun e he0=>?_
  refine wp_scalar (P := fun f=>Only [.x6] e f ∧ f.gpr .x6=13) (is := [.movz .x .x6 13 0]) rfl
    (wp_movz fun f hf h6=>wp_nil ⟨hf,h6⟩) fun f ⟨hf,h6⟩ hfv=>
    wp_vop (d := .v18) rfl fun g hg=>?_
  refine wp_scalar (P := fun h=>Only [.x6] g h ∧ h.gpr .x6=5) (is := [.movz .x .x6 5 0]) rfl
    (wp_movz fun h hh h5=>wp_nil ⟨hh,h5⟩) fun h ⟨hh,h5⟩ hhv=>
    wp_vop (d := .v19) rfl fun t ht=>wp_nil ?_
  have hk := ((((((((InitKeep.ofV ha (by decide)).trans (InitKeep.ofV hb (by decide))).trans
    (InitKeep.ofV hc (by decide))).trans (InitKeep.ofV hd (by decide))).trans
    (InitKeep.ofV he0 (by decide))).trans (InitKeep.ofOnly hf hfv)).trans
    (InitKeep.ofV hg (by decide))).trans (InitKeep.ofOnly hh hhv)).trans (InitKeep.ofV ht (by decide))
  refine ⟨hk.mono (by decide) (by decide),?_⟩
  constructor
  · rw [ht.other .v23 (by decide),hhv,hg.other .v23 (by decide),hfv,he0.other .v23 (by decide),hd.other .v23 (by decide),hc.other .v23 (by decide),hb.other .v23 (by decide),ha.v]
    rw [h11]
    rfl
  · rw [ht.other .v22 (by decide),hhv,hg.other .v22 (by decide),hfv,he0.other .v22 (by decide),hd.other .v22 (by decide),hc.other .v22 (by decide),hb.v]
    rw [ha.gpr,h15]
    rcases he with rfl|rfl <;> rfl
  · rw [ht.other .v21 (by decide),hhv,hg.other .v21 (by decide),hfv,he0.other .v21 (by decide),hd.other .v21 (by decide),hc.v]
    rw [hb.gpr,ha.gpr,h9]
    rfl
  · rw [ht.other .v20 (by decide),hhv,hg.other .v20 (by decide),hfv,he0.v]
    rw [hd.v,hd.other .v21 (by decide),hc.v,hc.gpr,hb.gpr,ha.gpr,h10,h9]
    rcases he with rfl|rfl <;> rfl
  · rw [ht.other .v18 (by decide),hhv,hg.v]
    rw [h6]
    rfl
  · rw [ht.v]
    rw [h5]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorSetup)

def setupFooter : List Instr :=
 [.movz .x .x0 0 0,.movz .x .x16 4 0,.addImm .x .x12 .x19 3000,.addImm .x .x12 .x12 3000]

theorem setupFooter_ok (s : State) :
    WP isa (.block setupFooter) s fun t=>InitKeep [.x0,.x16,.x12] [] s t ∧
      t.gpr .x0=0 ∧ t.gpr .x16=4 ∧ t.gpr .x12=s.gpr .x19+6000 := by
  let P : State→Prop := fun t=>Only [.x0,.x16,.x12] s t ∧
    t.gpr .x0=0 ∧ t.gpr .x16=4 ∧ t.gpr .x12=s.gpr .x19+6000
  apply WP.mono (WP.keepV (is := setupFooter) (Q := P) (by decide) ?_)
  · intro t ⟨⟨ho,h0,h16,h12⟩,hv⟩
    exact ⟨InitKeep.ofOnly ho hv,h0,h16,h12⟩
  change WP isa (.block setupFooter) s P
  dsimp only [P]
  unfold setupFooter
  refine wp_movz fun a ha h0=>wp_movz fun b hb h16=>
    wp_addImm (by decide) fun c hc h12=>wp_addImm (by decide) fun t ht h12'=>wp_nil ?_
  refine ⟨(((ha.trans hb).trans hc).trans ht).mono (by decide),?_,?_,?_⟩
  · rw [ht.get .x0,hc.get .x0,hb.get .x0,h0]; rfl
  · rw [ht.get .x16,hc.get .x16,h16]; rfl
  · rw [h12',h12,hb.get .x19,ha.get .x19,BitVec.add_assoc]; rfl

theorem vectorSetup_eq (η : Nat) : vectorSetup η=
    pairSetup .v25 0xffffff01ffffff00 0xffffff03ffffff02 ++ middleSetup ++
      pairSetup .v24 0x0000000200000001 0x0000000800000004 ++ setupFooter := rfl

theorem initWord_lane (x : BitVec 32) {e : Nat} (he : e<4) : vword (initWord x) e=x := by
  unfold initWord
  rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  rcases (show e=0∨e=1∨e=2∨e=3 by omega) with rfl|rfl|rfl|rfl <;> rfl

private theorem weights_lane : ∀e<4,
    vword (ofVDwords 0x0000000200000001 0x0000000800000004) e=BitVec.ofNat 32 (2^e) := by decide

theorem vectorSetup_ok {s : State} {η : Nat} (he : η=2∨η=4)
    (h9 : s.gpr .x9=BitVec.ofNat 64 Spec.MlDsa.q)
    (h10 : s.gpr .x10=BitVec.ofNat 64 η) (h11 : s.gpr .x11=15)
    (h15 : s.gpr .x15=BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.rbB η)) :
    WP isa (.block (vectorSetup η)) s fun t=>
      InitKeep [.x0,.x6,.x7,.x12,.x16] constantVecs s t ∧ Consts η (s.gpr .x19+6000) t := by
  rw [vectorSetup_eq,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (pairSetup_ok s .v25 _ _ (by decide)) fun a ⟨ha,h25⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (middleSetup_ok he (by rw [ha.keep.gpr .x9 (by decide)]; exact h9)
    (by rw [ha.keep.gpr .x10 (by decide)]; exact h10)
    (by rw [ha.keep.gpr .x11 (by decide)]; exact h11)
    (by rw [ha.keep.gpr .x15 (by decide)]; exact h15)) fun b ⟨hb,hbC⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (pairSetup_ok b .v24 _ _ (by decide)) fun c ⟨hc,h24⟩=>?_
  refine WP.mono (setupFooter_ok c) fun t ⟨ht,h0,h16,h12⟩=>?_
  have hk := ((ha.trans hb).trans hc).trans ht
  have hc19 : c.gpr .x19=s.gpr .x19 := ((ha.trans hb).trans hc).keep.gpr _ (by decide)
  refine ⟨hk.mono (by decide) (by decide),?_⟩
  constructor
  · exact h0
  · rw [hk.keep.gpr .x11 (by decide)]; exact h11
  · rw [h12,hc19]
  · exact h16
  · intro e he
    rw [ht.vec .v18 (by decide),hc.vec .v18 (by decide),hbC.thirteen,initWord_lane _ he]
    rfl
  · intro e he
    rw [ht.vec .v19 (by decide),hc.vec .v19 (by decide),hbC.five,initWord_lane _ he]
    rfl
  · intro e he
    rw [ht.vec .v20 (by decide),hc.vec .v20 (by decide),hbC.etaQ,initWord_lane _ he]
  · intro e he
    rw [ht.vec .v21 (by decide),hc.vec .v21 (by decide),hbC.q,initWord_lane _ he]
    rfl
  · intro e he
    rw [ht.vec .v22 (by decide),hc.vec .v22 (by decide),hbC.bound,initWord_lane _ he]
  · rw [ht.vec .v23 (by decide),hc.vec .v23 (by decide),hbC.nibble]
  · intro e he
    rw [ht.vec .v24 (by decide),h24]
    exact weights_lane e he
  · rw [ht.vec .v25 (by decide),hc.vec .v25 (by decide),hb.vec .v25 (by decide),h25]
    rfl
  · rw [hk.keep.gpr .x9 (by decide)]; exact h9
  · rw [hk.keep.gpr .x10 (by decide)]; exact h10
  · rw [hk.keep.gpr .x15 (by decide)]; exact h15

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
