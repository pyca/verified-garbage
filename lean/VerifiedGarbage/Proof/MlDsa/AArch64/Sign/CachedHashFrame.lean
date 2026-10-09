import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashPost
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentHash

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)
open VG.Impl.MlDsa.AArch64.Call (sc callAt)
open VG.Proof.MlDsa.Sign
open VG.Spec.Sha3 (bytesAt)

theorem hashFrameChk {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87) :
    icwChk p (hashWritePtrs p) p.k=true ∧
    (∀w∈hashWritePtrs p,inB (sgW p) w.1 w.2=true) := by
  rcases hp with rfl|rfl <;> decide

/-- The helper preserves the commitment inputs and produces its exact digest. -/
theorem hashReady_phase {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {σ s : State} {t : Nat}
    (h : PositiveICh p S σ t p.k s) :
    WP isa (callAt (if p.ℓ=5 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87")
      (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p)) (hashArgs p)) s
      (fun u => PositiveIC p S σ t u ∧
        PolyIs u.mem (pa u t4P)
          (toRq (bitUnpack (H (commitTailSeed s.mem (pa s (sc oMS)) (s.gpr .x9)) 640)
            524287 524288))) := by
  refine WP.mono_syms (hashReady_post hp hS h.c.masks.l.st.lay)
    fun u ⟨hP,hct,hm⟩ hy => ⟨⟨h.c.step hP hy (hashFrameChk hp).1 (hashFrameChk hp).2,?_⟩,?_⟩
  · rw [hP.pa (by decide),hct,Nat.mul_comm p.k,h.w1,h.c.masks.l.st.mu]
    simp only [CTv,ctF,w1Encode,List.flatMap_map]
  · rw [hP.pa (by decide)]
    exact hm

end VG.Proof.MlDsa.AArch64.Sign.Cached
