import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_addImm wp_movz)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (bReg)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Four (squeezeSetup)

def sixthOffsets : List Instr :=
  [.addImm .x .x24 .x24 840,.addImm .x .x25 .x25 840,
   .addImm .x .x26 .x26 840,.addImm .x .x27 .x27 840,.movz .x .x28 1 0]

theorem sixthOffsets_ok (s : State) : WP isa (.block sixthOffsets) s fun t =>
    Only [.x24,.x25,.x26,.x27,.x28] s t ∧
      (∀k<4,t.gpr (bReg k)=s.gpr (bReg k)+840) ∧ t.gpr .x28=1 := by
  unfold sixthOffsets
  refine wp_addImm (by decide) fun a ha ea => wp_addImm (by decide) fun b hb eb =>
    wp_addImm (by decide) fun c hc ec => wp_addImm (by decide) fun d hd ed =>
      wp_movz fun t ht et => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ((((ha.trans hb).trans hc).trans hd).trans ht).mono (by simp)
  · intro k hk
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl | rfl | rfl | rfl
    · change t.gpr .x24=s.gpr .x24+840
      rw [ht.get .x24,hd.get .x24,hc.get .x24,hb.get .x24,ea]; rfl
    · change t.gpr .x25=s.gpr .x25+840
      rw [ht.get .x25,hd.get .x25,hc.get .x25,eb,ha.get .x25]; rfl
    · change t.gpr .x26=s.gpr .x26+840
      rw [ht.get .x26,hd.get .x26,ec,hb.get .x26,ha.get .x26]; rfl
    · change t.gpr .x27=s.gpr .x27+840
      rw [ht.get .x27,ed,hc.get .x27,hb.get .x27,ha.get .x27]; rfl
  · rw [et]; rfl

theorem sixthSetup_ok (s : State) : WP isa (.block (squeezeSetup 840 1)) s fun t =>
    Only [.x22,.x23,.x24,.x25,.x26,.x27,.x28] s t ∧
      t.gpr .x22=s.gpr .x19 ∧ t.gpr .x23=s.gpr .x19+400 ∧
      (∀k<4,t.gpr (bReg k)=s.gpr .x19+BitVec.ofNat 64 (840+1008*k+840)) ∧
      t.gpr .x28=1 := by
  rw [show squeezeSetup 840 1=(squeezeSetup 0 0).take 6++sixthOffsets from rfl,
    WP.block_append_iff]
  refine WP.mono (squeezePointers_ok s) fun a ⟨ha,h22,h23,hbuf⟩ => ?_
  refine WP.mono (sixthOffsets_ok a) fun t ⟨ht,hptr,h28⟩ => ?_
  refine ⟨(ha.trans ht).mono (by simp),?_,?_,?_,h28⟩
  · rw [ht.get .x22,h22]
  · rw [ht.get .x23,h23]; rfl
  · intro k hk
    rw [hptr k hk,hbuf k hk]
    change (s.gpr .x19+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 840=_
    rw [Offset.add_add]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
