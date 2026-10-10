import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackConst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWidth

/-! ## From `KeygenPackFourConst.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_vop)

structure FourTableKeep (d : VReg) (s t : State) : Prop where
  gpr : ∀r,r≠.x9 → r≠.x10 → t.gpr r=s.gpr r
  vec : ∀r,r≠d → t.v r=s.v r
  mem : t.mem=s.mem
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

def fourTableValue (xs : List Nat) : BitVec 128 :=
  ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl (fun v i=>v+xs[i]!*2^(8*i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun v i=>v+xs[8+i]!*2^(8*i)) 0))

theorem fourTable_ok (s : State) (d : VReg) (xs : List Nat) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.KeygenPack.tblc d xs)) s fun t=>
      FourTableKeep d s t ∧ t.v d=fourTableValue xs := by
  unfold Impl.MlDsa.AArch64.Optimized.KeygenPack.tblc
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x9 _) fun a ha=>?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok a .x10 _) fun b hb=>?_
  refine wp_vop (d:=d) rfl fun c hc=>wp_vop (d:=d) rfl fun t ht=>WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r h9 h10=>?_,fun r hr=>?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,hc.gpr,hb.2.1 r h10,ha.2.1 r h9]
    · rw [ht.other r hr,hc.other r hr,hb.2.2,ha.2.2]
    · rw [ht.mem,hc.mem,hb.2.2,ha.2.2]
    · rw [ht.rd,hc.rd,hb.2.2,ha.2.2]
    · rw [ht.wr,hc.wr,hb.2.2,ha.2.2]
    · rw [ht.sp,hc.sp,hb.2.2,ha.2.2]
  · rw [ht.v,hc.gpr,hb.1,hc.v,hb.2.1 .x9 (by decide),ha.1]
    exact setLane_pair_hi _ _ _

theorem fourGatherTable_value :
    fourTableValue [0,4,8,12,16,20,24,28,32,36,40,44,48,52,56,60]=fourGatherIndex := by
  decide +kernel

theorem fourPackTable_value :
    fourTableValue [0,1,4,5,8,9,12,13,255,255,255,255,255,255,255,255]=fourPackIndex := by
  decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourSetup.lean` -/

section

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

end
