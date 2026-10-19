module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchPlan
import VerifiedGarbage.Proof.Framework.Omega

/-! # Controller updates preserve the persistent search payload -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem SearchMemory.stable {p : SearchPlan} {W : Nat → BitVec 64} :
    SearchPayload p.C (SearchMemory p W) := by
  intro s t h hf hk
  have ff : Frame [⟨p.C, 24⟩] s.mem t.mem := by
    intro a ha
    apply hf a
    right
    have hn := ha ⟨p.C, 24⟩ (by simp)
    change ¬ ofs p.C a < 24 at hn
    omega
  obtain ⟨V, R⟩ := h.rep
  have Rt := rep_of_disjoint_frame R ff
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.frameControl)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.hashControl)
  exact h.frame (lay_of_rep h.layout R Rt rfl hk.sp hk.wr) ⟨V, Rt⟩
    (fun _ _ => rfl) (ff.mono (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])) hk.rd hk.wr

end VG.Proof.Dsa.AArch64.Generation
