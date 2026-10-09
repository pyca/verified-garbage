import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)

theorem Rows.congr {v blocks : Nat} {σ s : State} {L R : Nat → List Zq}
    (h : Rows v blocks σ L s) (hr : ∀k<v,L k=R k) : Rows v blocks σ R s := by
  refine ⟨h.env,h.blockBound,h.pairs,h.bytes,?_,?_,?_⟩
  · intro k hk; rw [←hr k hk]; exact h.length k hk
  · intro k hk; rw [←hr k hk]; exact h.counts k hk
  · intro k hk; rw [←hr k hk]; exact h.stored k hk

theorem batchFour_ok {blocks off n : Nat} {σ s : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (h : Rows 4 blocks σ L s)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch variant off n) s
      (Rows 4 blocks σ (fun k => rowResult σ k off n (L k))) := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch
  apply WP.seq
  refine WP.mono (rowStep_ok hp h (by decide : 0<4) hn hmod variant) fun s1 h1 => ?_
  apply WP.seq
  refine WP.mono (rowStep_ok hp h1 (by decide : 1<4) hn hmod variant) fun s2 h2 => ?_
  apply WP.seq
  refine WP.mono (rowStep_ok hp h2 (by decide : 2<4) hn hmod variant) fun s3 h3 => ?_
  refine WP.mono (rowStep_ok hp h3 (by decide : 3<4) hn hmod variant) fun _ ht => ?_
  apply ht.congr
  intro k hk
  rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl | rfl | rfl | rfl <;>
    rfl

theorem batchTwo_ok {blocks off n : Nat} {σ s : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (h : Rows 2 blocks σ L s)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch variant off n) s
      (Rows 2 blocks σ (fun k => rowResult σ k off n (L k))) := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch
  apply WP.seq
  refine WP.mono (rowStep_ok hp h (by decide : 0<2) hn hmod variant) fun s1 h1 => ?_
  refine WP.mono (rowStep_ok hp h1 (by decide : 1<2) hn hmod variant) fun _ ht => ?_
  apply ht.congr
  intro k hk
  rcases (show k=0 ∨ k=1 by omega) with rfl | rfl <;>
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
