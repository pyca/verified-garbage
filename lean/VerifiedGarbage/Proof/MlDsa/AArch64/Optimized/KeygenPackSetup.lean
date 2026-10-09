import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackLoad
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
open VG.Proof.MlKem.AArch64 (Keep wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.ResidentMask (ConstKeep)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep repeatedWord repeatedWord_lane)

theorem vc_ok (s : State) (d : VReg) (n : Nat) :
    WP isa (.block (vc d n)) s fun t=>ConstKeep d s t ∧ t.v d=repeatedWord n := by
  rw [vc,WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x9 (BitVec.ofNat 64 n)) fun a ha=>?_
  refine wp_vop (d:=d) rfl fun t ht=>WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r hr=>?_,fun r hr=>?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,ha.2.1 r hr]
    · rw [ht.other r hr,ha.2.2]
    · rw [ht.mem,ha.2.2]
    · rw [ht.rd,ha.2.2]
    · rw [ht.wr,ha.2.2]
    · rw [ht.sp,ha.2.2]
  · rw [ht.v,ha.1]
    simp [repeatedWord]

theorem constants_ok (s : State) (b : Nat) :
    WP isa (.block (vc .v16 b ++ vc .v17 8380417)) s fun t=>
      SetupKeep [.v16,.v17] s t ∧ Constants b t := by
  rw [WP.block_append_iff]
  refine WP.mono (vc_ok s .v16 b) fun a ha=>?_
  refine WP.mono (vc_ok a .v17 8380417) fun t ht=>?_
  refine ⟨(SetupKeep.ofConst ha.1).trans (SetupKeep.ofConst ht.1),?_,?_⟩
  · intro e he
    rw [ht.1.vec .v16 (by decide),ha.2,repeatedWord_lane _ he]
  · intro e he
    rw [ht.2,repeatedWord_lane _ he]

theorem setup_ok (signed : Bool) (b : Nat) (s : State) :
    WP isa (.block (setup signed b)) s fun t=>
      Keep [.x2,.x9] s t ∧ t.mem=s.mem ∧
      t.gpr .x2=(if signed then s.gpr .x3 else s.gpr .x2) ∧
      (signed=true → Constants b t) := by
  cases signed
  · exact WP.block_nil_iff.mpr ⟨Keep.refl _ _,rfl,rfl,by simp⟩
  · simp only [setup,↓reduceIte,List.cons_append,List.nil_append]
    refine VG.Proof.MlKem.AArch64.wp_mov fun a ha h2=>?_
    refine WP.mono (constants_ok a b) fun t ⟨ht,hc⟩=>?_
    refine ⟨?_,ht.mem.trans ha.mem,?_,fun _=>hc⟩
    · exact ⟨fun r hr=>by rw [ht.gpr r (by simp_all),ha.gpr r (by simp_all)],
        ht.rd.trans ha.rd,ht.wr.trans ha.wr,ht.sp.trans ha.sp,fun r hr=>by
          rw [ht.vec r (by rcases r <;> simp_all [preservedV])];exact ha.vcs r hr⟩
    · rw [ht.gpr .x2 (by decide),h2]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
