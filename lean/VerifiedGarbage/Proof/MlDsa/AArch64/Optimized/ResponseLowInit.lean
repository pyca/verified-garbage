import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowReady
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)

def lowInit (g : Nat) : List Instr :=
  VG.Impl.MlDsa.AArch64.Optimized.HighPack.constants g ++
  VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc .v25 4194304 ++
  VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc .v26 4190208 ++
  [.vop (.dup .s4 .v24 .x4),.vop (.movi0 .v31)] ++
  VG.Impl.MlDsa.AArch64.Optimized.Response.normConstants

theorem lowInit_ok {g B : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (hB : 1≤B) {s : State} (hb : (s.gpr .x4).setWidth 32=BitVec.ofNat 32 B) :
    WP isa (.block (lowInit g)) s fun t =>
      SetupKeep [.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v25,.v26,.v24,.v31,.v27] s t ∧
      LowReady g B t ∧ t.v .v31=0 := by
  unfold lowInit
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.constants_ok s g) fun a ⟨hka,h16,h17,h18,h19,h20,h21,_,_⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok a .v25 4194304) fun b hb25 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok b .v26 4190208) fun c hc26 => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v24) rfl fun d hd => wp_vop (d := .v31) rfl fun e he => ?_
  refine WP.mono (normConstants_ok e) fun t ⟨ht,hlo,hw⟩ => ?_
  have hat : SetupKeep [.v25,.v26,.v24,.v31,.v27] a t := setup_mono
    ((((SetupKeep.ofConst hb25.1).trans (SetupKeep.ofConst hc26.1)).trans
      (setup_ofChg (hd.chg.trans he.chg))).trans ht) (by decide)
  have hbound : ∀i<4,vword (e.v .v24) i=BitVec.ofNat 32 B := by
    intro i hi
    rw [he.other .v24 (by decide),hd.v,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ hi,
      hc26.1.gpr .x4 (by decide),hb25.1.gpr .x4 (by decide),hka.gpr .x4 (by decide)]
    rcases (show i=0∨i=1∨i=2∨i=3 by omega) with rfl|rfl|rfl|rfl <;> exact hb
  have hsub : BitVec.ofNat 32 B-(1 : BitVec 32)=BitVec.ofNat 32 (B-1) := by
    bv_omega
  refine ⟨setup_mono (hka.trans hat) (by decide),?_,?_⟩
  · constructor
    · constructor
      · intro i hi; rw [hat.vec .v17 (by decide),h17,HighPack.repeatedWord_lane _ hi]
      · intro i hi; rw [hat.vec .v18 (by decide),h18,HighPack.repeatedWord_lane _ hi]
        rcases hg with rfl|rfl <;> rfl
      · intro i hi; rw [hat.vec .v19 (by decide),h19,HighPack.repeatedWord_lane _ hi]
        rcases hg with rfl|rfl <;> rfl
      · intro i hi; rw [hat.vec .v20 (by decide),h20,HighPack.repeatedWord_lane _ hi]
    · intro i hi; rw [hat.vec .v16 (by decide),h16,HighPack.repeatedWord_lane _ hi]
    · intro i hi
      rw [ht.vec .v25 (by decide),he.other .v25 (by decide),hd.other .v25 (by decide),
        hc26.1.vec .v25 (by decide),hb25.2,HighPack.repeatedWord_lane _ hi]
    · intro i hi
      rw [ht.vec .v26 (by decide),he.other .v26 (by decide),hd.other .v26 (by decide),
        hc26.2,HighPack.repeatedWord_lane _ hi]
    · intro i hi; rw [hat.vec .v21 (by decide),h21,HighPack.repeatedWord_lane _ hi]
    · intro i hi; rw [hlo i hi,hbound i hi,hsub]
    · intro i hi
      rw [hw i hi,hbound i hi,hsub,← BitVec.ofNat_add]
      congr 1; omega
  · rw [ht.vec .v31 (by decide),he.v]

end VG.Proof.MlDsa.AArch64.Optimized.Response
