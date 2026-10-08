import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.LoopStep
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.FinalCommon

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)
open VG.Impl.Gcm.X86_64.StitchAvx8 (batch q8 finish)

theorem finalDec_ok {s₀ s : State} {P : Nat → Block} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ P true g s) (hn : nb s₀ = g + 8) :
    WP isa (.seq (batch (nr s₀) 8 0 (q8 (nr s₀) false)) (.block finish)) s (DPost s₀) := by
  have hc : CoreInv s₀ P true g g s := h.core
  refine WP.seq (WP.mono (hc.hashBatch hp (by simp [lead]) h.buffered false (by omega)
    (fun he => Bool.noConfusion he)) fun t ht => ?_)
  have hd := hc.data.batch hp (by omega) (by simpa only [lead, Bool.true_eq, ite_true, Nat.mul_zero,
    BitVec.add_zero] using hc.cursor) ht
  rw [← hn] at hd
  refine finish_complete hp true ht.env hd ?_ ?_
  · rw [ht.counter, hn]
  · rw [ht.hash, hlaw]
    change Spec.Gcm.ghashFrom (hk s₀) (hashPrefix s₀ true g) ((List.range 8).map (window s₀ true g)) = _
    rw [hn]
    exact (ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ true) g).symm

end VG.Proof.Gcm.X86_64.StitchAvx8
