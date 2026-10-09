import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackFourGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackConst

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
