import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedConstants
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

/-! ## From `PairedHintConstants.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)
open VG.Proof.MlDsa.AArch64.Optimized.Response (setup_ofChg setup_mono)

def hintConstants : List Instr :=
  [.vop (.dup .s4 .v11 .x17),.vop (.movi0 .v13),
   .vop (.sub .s4 .v12 .v13 .v11),.vop (.movi0 .v14)]

theorem hintConstants_ok (s : State) : WP isa (.block hintConstants) s fun t =>
    SetupKeep [.v11,.v12,.v13,.v14] s t ∧ t.v .v13=0 ∧ t.v .v14=0 ∧
    (∀e<4,vword (t.v .v11) e=(s.gpr .x17).setWidth 32) ∧
    (∀e<4,vword (t.v .v12) e= -(s.gpr .x17).setWidth 32) := by
  unfold hintConstants
  refine wp_vop (d := .v11) rfl fun a ha => wp_vop (d := .v13) rfl fun b hb =>
    wp_vop (d := .v12) rfl fun c hc => wp_vop (d := .v14) rfl fun t ht =>
    WP.block_nil_iff.mpr ?_
  refine ⟨setup_mono (setup_ofChg (ha.chg.trans (hb.chg.trans (hc.chg.trans ht.chg)))) (by decide),
    by rw [ht.other .v13 (by decide),hc.other .v13 (by decide),hb.v],ht.v,?_,?_⟩
  · intro i hi
    rw [ht.other .v11 (by decide),hc.other .v11 (by decide),hb.other .v11 (by decide),ha.v]
    change vword (HighPack.repeatedWord (s.gpr .x17).toNat) i = _
    rw [HighPack.repeatedWord_lane _ hi]
    rfl
  · intro i hi
    rw [ht.other .v12 (by decide),hc.v,vword_map2 _ _ _ hi,hb.v,
      hb.other .v11 (by decide),ha.v]
    change vword 0 i-vword (HighPack.repeatedWord (s.gpr .x17).toNat) i = _
    rw [HighPack.repeatedWord_lane _ hi]
    have hz : vword 0 i=0 := by
      rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by omega) with rfl | rfl | rfl | rfl <;> rfl
    rw [hz]
    exact BitVec.zero_sub _

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedMiddle.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)
open VG.Proof.MlDsa.AArch64.Optimized.Response (setup_mono)

def middleMoves : List Instr := [.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0]

theorem middleMoves_ok (s : State) : WP isa (.block middleMoves) s fun t =>
    ((t.gpr .x0=s.gpr .x0-1024 ∧ t.gpr .x2=s.gpr .x0-1024 ∧
      t.gpr .x12=8 ∧ t.mem=s.mem) ∧ Keep [.x0,.x2,.x12] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold middleMoves mov
  arun
  exact ⟨rfl,rfl⟩

theorem zConstants_ok (g : Nat) (s : State)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32) :
    WP isa (.block (constants .z g)) s fun t =>
      SetupKeep [.v8,.v9,.v10,.v30] s t ∧ CheckReady false t ∧ t.v .v30=0 ∧
      (∀e<4,vword (t.v .v9) e=(s.gpr .x8).setWidth 32-1) ∧
      (∀e<4,vword (t.v .v10) e=(s.gpr .x8).setWidth 32+((s.gpr .x8).setWidth 32-1)) := by
  have he : constants .z g=commonConstants := by simp only [constants,commonConstants,List.append_nil]
  rw [he]
  refine WP.mono (commonConstants_ok s) fun t ⟨hf,hb,hz,hl,hu⟩ => ?_
  refine ⟨hf,⟨?_,?_,by simp,by simp⟩,hz,hl,hu⟩
  · rw [hf.vec .v31 (by decide)]; exact hq
  · intro e he
    rw [hb,HighPack.repeatedWord_lane _ he]

def constantRegs : List VReg := [.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v30]

theorem hConstants_ok (g : Nat) (s : State)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32) :
    WP isa (.block (constants .h g)) s fun t =>
      SetupKeep constantRegs s t ∧ CheckReady true t ∧ t.v .v30=0 ∧ t.v .v14=0 ∧
      (∀e<4,vword (t.v .v11) e=(s.gpr .x17).setWidth 32) ∧
      (∀e<4,vword (t.v .v9) e=(s.gpr .x8).setWidth 32-1) ∧
      (∀e<4,vword (t.v .v10) e=(s.gpr .x8).setWidth 32+((s.gpr .x8).setWidth 32-1)) := by
  change WP isa (.block (commonConstants++hintConstants)) s _
  rw [WP.block_append_iff]
  refine WP.mono (commonConstants_ok s) fun a ⟨ha,hbias,hflag,hl,hu⟩ => ?_
  refine WP.mono (hintConstants_ok a) fun t ⟨ht,hzero,hcount,hgamma,hneg⟩ => ?_
  have hf : SetupKeep constantRegs s t := setup_mono (ha.trans ht) (by decide)
  refine ⟨hf,⟨?_,?_,?_,?_⟩,?_,hcount,?_,?_,?_⟩
  · rw [hf.vec .v31 (by decide)]; exact hq
  · intro e he
    rw [ht.vec .v8 (by decide),hbias,HighPack.repeatedWord_lane _ he]
  · intro _ e he
    rw [hneg e he,hgamma e he]
  · intro _ e he
    rw [hzero]
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  · rw [ht.vec .v30 (by decide),hflag]
  · intro e he
    rw [hgamma e he,ha.gpr .x17 (by decide)]
  · rw [ht.vec .v9 (by decide)]; exact hl
  · rw [ht.vec .v10 (by decide)]; exact hu

theorem r0Constants_ok (g : Nat) (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) (s : State)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32) :
    WP isa (.block (constants .r0 g)) s fun t =>
      SetupKeep constantRegs s t ∧ LowReady g t ∧ t.v .v30=0 ∧
      (∀e<4,vword (t.v .v15) e=BitVec.ofNat 32 (2*g)) ∧
      (∀e<4,vword (t.v .v9) e=(s.gpr .x8).setWidth 32-1) ∧
      (∀e<4,vword (t.v .v10) e=(s.gpr .x8).setWidth 32+((s.gpr .x8).setWidth 32-1)) := by
  change WP isa (.block (commonConstants++lowConstants g)) s _
  rw [WP.block_append_iff]
  refine WP.mono (commonConstants_ok s) fun a ⟨ha,hbias,hflag,hl,hu⟩ => ?_
  refine WP.mono (lowConstants_ok g a) fun t ⟨ht,h11,h12,h13,h14,h15⟩ => ?_
  have hf : SetupKeep constantRegs s t := setup_mono (ha.trans ht) (by decide)
  refine ⟨hf,⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · rw [hf.vec .v31 (by decide)]; exact hq
  · intro e he
    rw [ht.vec .v8 (by decide),hbias,HighPack.repeatedWord_lane _ he]
  · intro e he
    rw [h11,HighPack.repeatedWord_lane _ he]
  · intro e he
    rw [h12,HighPack.repeatedWord_lane _ he]
    rcases hg with rfl | rfl <;> rfl
  · intro e he
    rw [h13,HighPack.repeatedWord_lane _ he]
    rcases hg with rfl | rfl <;> rfl
  · intro e he
    rw [h14,HighPack.repeatedWord_lane _ he]
  · rw [ht.vec .v30 (by decide),hflag]
  · intro e he
    rw [h15,HighPack.repeatedWord_lane _ he]
  · rw [ht.vec .v9 (by decide)]; exact hl
  · rw [ht.vec .v10 (by decide)]; exact hu

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
