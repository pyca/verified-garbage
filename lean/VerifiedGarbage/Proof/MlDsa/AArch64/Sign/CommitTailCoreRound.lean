import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCoreState

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.Sha3.AArch64.Sha3.Vector (rounds)

/-- Each inline permutation advances both unrelated sponge states. -/
theorem coreRound_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (h : CoreState σ wlen w1 work A B i s) :
    WP isa (.block rounds) s (RoundState σ wlen w1 work A B i i) := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Optimized.Resident.permute_ok h.pairs)
    fun t ⟨hk,hp⟩ => ?_
  refine ⟨⟨?_,?_,?_,?_⟩,hp⟩
  · refine ⟨fun r hr=>?_,hk.rd.trans h.keep.rd,hk.wr.trans h.keep.wr,hk.sp.trans h.keep.sp⟩
    exact (hk.gpr r (fun he=>hr (by simp [coreRegs,he]))).trans (h.keep.gpr r hr)
  · rw [hk.mem]; exact h.frame
  · rw [hk.gpr .x5 (by decide)]; exact h.ptr
  · rw [hk.mem]; exact h.output

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
