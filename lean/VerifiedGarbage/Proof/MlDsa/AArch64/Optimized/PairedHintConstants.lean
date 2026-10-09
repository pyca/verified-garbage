import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedConstants

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
