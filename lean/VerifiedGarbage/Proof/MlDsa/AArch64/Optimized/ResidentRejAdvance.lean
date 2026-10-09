import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejGuard

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- The two fixed pointer/count instructions following each vector batch. -/
theorem advance_ok (n : Nat) (hn : 3*n<4096) {s : State} :
    WP isa (.block [.addImm .x .x2 .x2 (3*n),.subImm .x .x5 .x5 n]) s fun t =>
      Only [.x2,.x5] s t ∧ t.v=s.v ∧
      t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (3*n) ∧
      t.gpr .x5=s.gpr .x5-BitVec.ofNat 64 n := by
  refine WP.mono (WP.keepV (Q := fun t => Only [.x2,.x5] s t ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (3*n) ∧
    t.gpr .x5=s.gpr .x5-BitVec.ofNat 64 n) (by rfl)
    (wp_addImm hn fun a ha ea => wp_subImm (by omega) fun t ht et => wp_nil ?_)) ?_
  · exact ⟨(ha.trans ht).mono (by decide),by rw [ht.get .x2]; exact ea,
      by rw [et,ha.get .x5]⟩
  · intro t ⟨⟨hf,h2,h5⟩,hv⟩; exact ⟨hf,hv,h2,h5⟩

/-- Scalar bookkeeping keeps the vector decoder constants intact. -/
theorem Constants.of_keep {s t : State} {rs : List Reg} (h : Constants s)
    (hk : Keep rs s t) (h9 : Reg.x9∉rs) (h12 : Reg.x12∉rs) (hv : t.v=s.v) :
    Constants t := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hv]; exact h.index
  · intro e he; rw [hv]; exact h.mask e he
  · intro e he; rw [hv]; exact h.modulus e he
  · rw [hk.get .x12 h12]; exact h.ones
  · rw [hk.get .x9 h9]; exact h.qreg

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
