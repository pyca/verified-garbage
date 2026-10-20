module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.PlainSimp

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowShared

abbrev savedLanes : List (Reg × VReg × Nat) :=
  (BlockedRedc.saved.zip vecs).map fun (r,v) => (r,v,0)

theorem save_ok (s : State) : WP isa (.block save) s fun t =>
    (t.mem = s.mem ∧ ∀ k ∈ savedLanes, laneOf t k.2.1 k.2.2 = s.gpr k.1) ∧ Keep [] s t := by
  refine WP.keep [] ?_ rfl rfl (by decide +kernel)
  change WP isa (.block (insOf savedLanes)) s _
  exact WP.mono (insOf_ok savedLanes s (by decide) (by decide))
    fun _ ⟨_,hm,_,_,_,hl,_⟩ => ⟨hm,hl⟩

theorem restore_ok (s : State) : WP isa (.block restore) s fun t =>
    (t.mem = s.mem ∧ ∀ k ∈ savedLanes, t.gpr k.1 = laneOf s k.2.1 k.2.2) ∧
      Keep BlockedRedc.saved s t := by
  refine WP.keep BlockedRedc.saved ?_ rfl rfl (by decide +kernel)
  change WP isa (.block (umovOf savedLanes)) s _
  exact WP.mono (umovOf_ok savedLanes s (by decide) (by decide))
    fun _ ⟨hm,_,_,_,hl,_⟩ => ⟨hm,hl⟩

theorem saved_lane_exists : ∀ r ∈ BlockedRedc.saved, ∃ v, (r,v,0) ∈ savedLanes := by
  intro r hr
  cases r <;> simp_all only [BlockedRedc.saved, BlockedRedc.aa,
    List.mem_append, List.mem_cons, List.mem_nil_iff, reduceCtorEq, or_false, false_or]
  all_goals first
    | exact ⟨.v0, by decide⟩
    | exact ⟨.v1, by decide⟩
    | exact ⟨.v2, by decide⟩
    | exact ⟨.v3, by decide⟩
    | exact ⟨.v4, by decide⟩
    | exact ⟨.v5, by decide⟩
    | exact ⟨.v6, by decide⟩
    | exact ⟨.v27, by decide⟩
    | exact ⟨.v28, by decide⟩
    | exact ⟨.v29, by decide⟩
    | exact ⟨.v30, by decide⟩

theorem work_keeps_vectors : ∀ k ∈ savedLanes, ∀ i ∈ instrs work, vdstOf i ≠ some k.2.1 := by
  have h : work.allInstrs (fun i => savedLanes.all fun k => vdstOf i != some k.2.1) = true := by
    decide +kernel
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  intro k hk i hi
  exact bne_iff_ne.mp ((List.all_eq_true.mp (h i hi)) k hk)

end VG.Proof.Bignum.AArch64.WindowShared
