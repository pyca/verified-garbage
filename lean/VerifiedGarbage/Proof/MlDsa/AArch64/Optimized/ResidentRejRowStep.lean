import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRows

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)

def updateRow (L : Nat → List Zq) (k : Nat) (R : List Zq) : Nat → List Zq :=
  fun j => if j=k then R else L j

theorem rowStep_ok {v blocks k off n : Nat} {σ s : State} {L : Nat → List Zq}
    (hp : Pre v σ) (h : Rows v blocks σ L s) (hk : k<v)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.segment variant k off n) s
      (Rows v blocks σ (updateRow L k (rowResult σ k off n (L k)))) := by
  refine WP.mono (segmentEnv_ok hp h.env hk (by have:=h.blockBound; omega) hmod
    (h.length k hk) (h.counts k hk) (h.stored k hk) variant) fun t ⟨he,hf,hc,hs⟩ => ?_
  rw [segmentResult_rows h hk hn] at hc hs
  refine ⟨he,h.blockBound,?_,?_,?_,?_,?_⟩
  · intro p hpv
    exact segment_pair_keep hp hk hpv hf (h.pairs p hpv)
  · intro j hj d hd
    rw [segment_buffer_keep hp hk hj (by have:=h.blockBound; omega) hf]
    exact h.bytes j hj d hd
  · intro j hj
    by_cases heq : j=k
    · subst j
      simpa only [updateRow,ite_true,rowResult,Spec.MlDsa.n] using rnFold_length_le (h.length k hk) (streamBytes σ k off (3*n))
    · simpa only [updateRow,ite_eq_right_iff.mpr (fun ht => False.elim (heq ht))] using h.length j hj
  · intro j hj
    by_cases heq : j=k
    · subst j
      simpa only [updateRow,ite_true] using hc
    · rw [segment_count_keep hp hk hj heq hf]
      simpa only [updateRow,ite_eq_right_iff.mpr (fun ht => False.elim (heq ht))] using h.counts j hj
  · intro j hj
    by_cases heq : j=k
    · subst j
      simpa only [updateRow,ite_true] using hs
    · have hx := segment_stored_keep hp hk hj heq hf (h.length j hj) (h.stored j hj)
      simpa only [updateRow,ite_eq_right_iff.mpr (fun ht => False.elim (heq ht))] using hx

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
