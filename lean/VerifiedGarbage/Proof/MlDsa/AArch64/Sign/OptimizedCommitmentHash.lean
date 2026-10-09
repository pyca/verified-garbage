import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedCommitment
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentPack

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlDsa.Sign
open VG.Spec.Sha3 (bytesAt)

structure PositiveIC (p : Params) (S : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : PositiveICw p S σ t p.k s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p)=CTv p σ (p.ℓ*t)

theorem commitmentHashWrites_ok {p : Params} (hp : Ok3 p) :
    ∀w∈[(sc 0,200),(sc 200,640),(sc oCT,cLen p)],inB (sgW p) w.1 w.2=true := by
  rcases hp with rfl | rfl | rfl <;> decide

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem positiveCommitmentHash_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {σ s : State} {t : Nat} (h : PositiveICh p S σ t p.k s) :
    WP isa (shakeAtWith keccak.callee [⟨.x26,0,64⟩,⟨.x28,oW1,p.k*w1Len p⟩]
      ⟨.x28,oCT,cLen p⟩) s (PositiveIC p S σ t) := by
  have hc := cChk_ok hp
  simp only [cChk,Bool.and_eq_true] at hc
  obtain ⟨⟨_,hs⟩,hk⟩ := hc
  refine WP.mono_syms (shake_ok hP.s16 hP.s64 h.c.masks.l.st.lay (by simp) hs)
    fun u ⟨hPu,_,hb⟩ hy => ⟨h.c.step hPu hy hk (commitmentHashWrites_ok hp),?_⟩
  rw [hPu.pa (by decide),hb]
  simp only [List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil]
  show H (bytesAt s.mem (pa s (.x26,0)) 64 ++ bytesAt s.mem (pa s (sc oW1)) (p.k*w1Len p)) (cLen p)=_
  rw [Nat.mul_comm p.k,h.w1,h.c.masks.l.st.mu]
  simp only [CTv,ctF,w1Encode,List.flatMap_map]

/-- Complete commitment generation with paired masks, direct-source NTTs,
fused matrix rows, and the existing packed commitment hash. -/
theorem positiveCommit_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {σ s : State} {t : Nat} (h : PositiveIL p S σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p) s (PositiveIC p S σ t) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.commitWith
  refine WP.seq (WP.mono (positiveMasks_ok hP (positiveMasksChk_ok hp) h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (positiveRows_ok hp h1) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (positivePackRows_ok hP hp h2) fun s3 h3 => ?_)
  exact positiveCommitmentHash_ok hP hp h3

end VG.Proof.MlDsa.AArch64.Sign
