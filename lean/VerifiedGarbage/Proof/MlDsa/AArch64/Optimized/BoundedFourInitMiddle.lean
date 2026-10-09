import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitWord

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
