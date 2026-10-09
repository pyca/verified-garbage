import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPrefix

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

private theorem afterFirst {v : Nat} {σ s : State}
    (h : Rows v 5 σ (fun k => rowResult σ k 0 168 []) s) :
    Rows v 5 σ (fun k => prefixRow σ k 504) s := h.congr (fun _ _ => rfl)

private theorem afterSecond {v : Nat} {σ s : State}
    (h : Rows v 5 σ (fun k => rowResult σ k 504 112 (prefixRow σ k 504)) s) :
    Rows v 5 σ (fun k => prefixRow σ k 840) s :=
  h.congr (fun k _ => rowResult_prefix σ k 504 112 (by decide))

theorem parseFiveFour_ok {σ s : State} (hp : Pre 4 σ) (h : FirstBlocks 4 σ s) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 0 168)
      (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 504 112)) s
      (Rows 4 5 σ (fun k => prefixRow σ k 840)) := by
  apply WP.seq
  refine WP.mono (batchFour_ok hp h.rows (by decide : 0+3*168≤168*5) (by decide) 0)
    fun _ ht => ?_
  exact WP.mono (batchFour_ok hp (afterFirst ht) (by decide : 504+3*112≤168*5) (by decide) 0)
    fun _ hu => afterSecond hu

theorem parseFiveTwo_ok {σ s : State} (hp : Pre 2 σ) (h : FirstBlocks 2 σ s) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 0 168)
      (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 504 112)) s
      (Rows 2 5 σ (fun k => prefixRow σ k 840)) := by
  apply WP.seq
  refine WP.mono (batchTwo_ok hp h.rows (by decide : 0+3*168≤168*5) (by decide) 0)
    fun _ ht => ?_
  exact WP.mono (batchTwo_ok hp (afterFirst ht) (by decide : 504+3*112≤168*5) (by decide) 0)
    fun _ hu => afterSecond hu

theorem parseSixthFour_ok {σ s : State} (hp : Pre 4 σ)
    (h : Rows 4 6 σ (fun k => prefixRow σ k 840) s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.batch 0 840 56) s
      (Rows 4 6 σ (fun k => prefixRow σ k 1008)) := by
  refine WP.mono (batchFour_ok hp h (by decide : 840+3*56≤168*6) (by decide) 0) fun _ ht => ?_
  exact ht.congr (fun k _ => rowResult_prefix σ k 840 56 (by decide))

theorem parseSixthTwo_ok {σ s : State} (hp : Pre 2 σ)
    (h : Rows 2 6 σ (fun k => prefixRow σ k 840) s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.batch 0 840 56) s
      (Rows 2 6 σ (fun k => prefixRow σ k 1008)) := by
  refine WP.mono (batchTwo_ok hp h (by decide : 840+3*56≤168*6) (by decide) 0) fun _ ht => ?_
  exact ht.congr (fun k _ => rowResult_prefix σ k 840 56 (by decide))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
