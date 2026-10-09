import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackInit

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)

theorem setup_ofChg {rs : List VReg} {s t : State} (h : VChg rs s t) : SetupKeep rs s t :=
  ⟨fun r _ => congrFun h.gpr r,h.v,h.mem,h.rd,h.wr,h.sp⟩
theorem setup_mono {rs rt : List VReg} {s t : State} (h : SetupKeep rs s t)
    (hm : ∀r∈rs,r∈rt) : SetupKeep rt s t :=
  ⟨h.gpr,fun r hr => h.vec r (fun hs => hr (hm r hs)),h.mem,h.rd,h.wr,h.sp⟩
theorem setup_keep {rs : List VReg} {s t : State} (h : SetupKeep rs s t)
    (hv : ∀r∈preservedV,r∉rs) : Keep [.x9] s t :=
  ⟨fun r hr => h.gpr r (by simpa only [List.mem_singleton] using hr),h.rd,h.wr,h.sp,
    fun r hr => by rw [h.vec r (hv r hr)]⟩

/-- Convert a broadcast bound B to B−1 and 2B−1, exactly as measured. -/
theorem normConstants_ok (s : State) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Optimized.Response.normConstants) s fun t =>
      SetupKeep [.v27,.v24] s t ∧
      (∀e<4,vword (t.v .v27) e=vword (s.v .v24) e-1) ∧
      (∀e<4,vword (t.v .v24) e=vword (s.v .v24) e+(vword (s.v .v24) e-1)) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Response.normConstants
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s .v27 1) fun a ha => ?_
  refine wp_vop (d := .v27) rfl fun b hb => wp_vop (d := .v24) rfl fun t ht =>
    WP.block_nil_iff.mpr ?_
  refine ⟨setup_mono ((SetupKeep.ofConst ha.1).trans (setup_ofChg (hb.chg.trans ht.chg))) (by decide),?_,?_⟩
  · intro e he
    rw [ht.other .v27 (by decide),hb.v,VG.AArch64.vword_map2 _ _ _ he,
      ha.1.vec .v24 (by decide),ha.2,HighPack.repeatedWord_lane _ he]
    rfl
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.get .v24 (by decide),
      hb.v,VG.AArch64.vword_map2 _ _ _ he,ha.1.vec .v24 (by decide),
      ha.2,HighPack.repeatedWord_lane _ he]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
