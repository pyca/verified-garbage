import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseHoisted
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFirstLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg VMem)
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.AArch64.Optimized.ResidentMask (ConstKeep)

def firstSetup : List Instr := [mov .x3 .x1,
  .addImm .x .x4 .x1 512,.addImm .x .x5 .x1 768,.addImm .x .x6 .x1 896,
  .addImm .x .x7 .x1 960,.movz .x .x11 8 0]
def firstInit : List Instr := VG.Impl.MlDsa.AArch64.Optimized.HighPack.vc .v31 8380417 ++ firstSetup

theorem firstSetup_ok (s : State) : WP isa (.block firstSetup) s fun t =>
    ((t.gpr .x11=8 ∧ t.mem=s.mem) ∧ Keep [.x3,.x4,.x5,.x6,.x7,.x11] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold firstSetup mov
  arun

theorem constKeep_keep {s t : State} {d : VReg} (h : ConstKeep d s t)
    (hd : d∉preservedV) : Keep [.x9] s t := by
  refine ⟨fun r hr => h.gpr r (by simpa using hr),h.rd,h.wr,h.sp,?_⟩
  intro r hr
  rw [h.vec r (fun he => hd (he ▸ hr))]

theorem firstInit_ok (s : State) : WP isa (.block firstInit) s fun t =>
    Keep [.x3,.x4,.x5,.x6,.x7,.x9,.x11] s t ∧ t.mem=s.mem ∧
    t.gpr .x11=8 ∧ (∀ e<4, vword (t.v .v31) e=8380417#32) := by
  unfold firstInit
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s .v31 8380417) fun a ha => ?_
  refine WP.mono (firstSetup_ok a) fun t ⟨⟨⟨h11,hm⟩,hk⟩,hv⟩ => ?_
  refine ⟨((constKeep_keep ha.1 (by decide)).trans hk).mono,hm.trans ha.1.mem,h11,?_⟩
  intro e he
  rw [hv,ha.2]
  exact HighPack.repeatedWord_lane _ he

def finalSetup : List Instr := [.subImm .x .x0 .x0 1024,mov .x2 .x0,.movz .x .x12 8 0]

theorem finalSetup_ok (s : State) : WP isa (.block finalSetup) s fun t =>
    ((t.gpr .x0=s.gpr .x0-1024 ∧ t.gpr .x2=s.gpr .x0-1024 ∧ t.gpr .x12=8 ∧ t.mem=s.mem) ∧
      Keep [.x0,.x2,.x12] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold finalSetup mov
  arun
  exact ⟨rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
