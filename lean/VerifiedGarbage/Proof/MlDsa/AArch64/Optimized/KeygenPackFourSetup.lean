import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourConst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWidth

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (repeatedWord_lane)

theorem FourTableKeep.keep {d : VReg} {s t : State} (h : FourTableKeep d s t)
    (hd : d∉preservedV) : Keep [.x9,.x10] s t := by
  refine ⟨fun r hr=>h.gpr r (by simp_all) (by simp_all),h.rd,h.wr,h.sp,?_⟩
  intro r hr
  rw [h.vec r (by intro he;subst r;exact hd hr)]

def fourSetup (signed : Bool) : List Instr :=
  setup signed 4 ++
  tblc .v18 [0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60] ++
  tblc .v19 [0,1,4,5,8,9,12,13,255,255,255,255,255,255,255,255] ++
  vc .v20 0x00ff00ff ++ [.movz .x .x15 16 0]

theorem fourSetup_ok (signed : Bool) (s : State) :
    WP isa (.block (fourSetup signed)) s fun t=>
      Keep [.x2,.x9,.x10,.x15] s t ∧ t.mem=s.mem ∧
      t.gpr .x2=(if signed then s.gpr .x3 else s.gpr .x2) ∧
      (signed=true → Constants 4 t) ∧ t.v .v18=fourGatherIndex ∧
      t.v .v19=fourPackIndex ∧ (∀e<4,vword (t.v .v20) e=0x00ff00ff) ∧ t.gpr .x15=16 := by
  unfold fourSetup
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (setup_ok signed 4 s) fun a ⟨ka,ma,oa,ca⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (fourTable_ok a .v18 _) fun b ⟨kb,hb⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (fourTable_ok b .v19 _) fun c ⟨kc,hc⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok c .v20 _) fun d ⟨kd,hd⟩=>?_
  refine WP.mono (counter_ok 16 (by decide) d) fun t ⟨⟨⟨ht,mt⟩,kt⟩,vt⟩=>?_
  have kk : Keep [.x9] c d := ⟨fun r hr=>kd.gpr r (by simpa using hr),kd.rd,kd.wr,kd.sp,
    fun r hr=>by rw [kd.vec r (by rcases r <;> simp_all [preservedV])]⟩
  refine ⟨((((ka.trans (kb.keep (by decide))).trans (kc.keep (by decide))).trans kk).trans kt).mono,
    mt.trans (kd.mem.trans (kc.mem.trans (kb.mem.trans ma))),?_,?_,?_,?_,?_,ht⟩
  · rw [kt.get .x2,kd.gpr .x2 (by decide),kc.gpr .x2 (by decide) (by decide),
      kb.gpr .x2 (by decide) (by decide),oa]
  · intro h
    exact ⟨by rw [vt,kd.vec .v16 (by decide),kc.vec .v16 (by decide),kb.vec .v16 (by decide)];exact (ca h).bias,
      by rw [vt,kd.vec .v17 (by decide),kc.vec .v17 (by decide),kb.vec .v17 (by decide)];exact (ca h).modulus⟩
  · rw [vt,kd.vec .v18 (by decide),kc.vec .v18 (by decide),hb,fourGatherTable_value]
  · rw [vt,kd.vec .v19 (by decide),hc,fourPackTable_value]
  · intro e he
    rw [vt,hd,repeatedWord_lane _ he]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
