import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTimingDone

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F)

abbrev TailReady (v : Nat) (σ s : State) := Done v σ s ∧
  ∀k<v,∀j<1008,s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j

theorem zeroTail_ready {v k : Nat} {σ s : State} (hp : Pre v σ)
    (h : TailReady v σ s) (hk : k<v) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.zeroTail k) s (TailReady v σ) := by
  refine WP.mono (zeroTail_frame_ok hp h.1 hk) fun t ⟨ht,hf⟩ => ⟨ht,?_⟩
  intro j hj d hd
  have hb : (scrR σ).Contains (bufP σ j+BitVec.ofNat 64 d) 1 := by
    change (scrR σ).Contains ((scr σ+BitVec.ofNat 64 (840+1008*j))+BitVec.ofNat 64 d) 1
    rw [Offset.add_add]
    exact Offset.contains_base (scr σ) (by have:=hp.streams; omega) (by have:=hp.streams; omega)
  rw [hf (bufP σ j+BitVec.ofNat 64 d) (by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact hp.a_scr.symm _ hb)]
  exact h.2 j hj d hd

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
