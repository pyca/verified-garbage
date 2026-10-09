import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatch

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F)

theorem streamBytes_length (σ : State) (k off n : Nat) :
    (streamBytes σ k off n).length=n := by simp only [streamBytes,List.length_map,List.length_range]

theorem streamBytes_append (σ : State) (k off a b : Nat) :
    streamBytes σ k off (a+b)=streamBytes σ k off a++streamBytes σ k (off+a) b := by
  simp only [streamBytes,List.range_add,List.map_append,List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply,Nat.add_comm,Nat.add_left_comm]

def prefixRow (σ : State) (k n : Nat) : List Spec.MlDsa.Zq :=
  rnFold [] (streamBytes σ k 0 n)

theorem rowResult_prefix (σ : State) (k off n : Nat) (hmod : off%3=0) :
    rowResult σ k off n (prefixRow σ k off)=prefixRow σ k (off+3*n) := by
  unfold rowResult prefixRow
  rw [streamBytes_append,rnFold_append _ _ _ (by rw [streamBytes_length]; exact hmod)]
  rw [Nat.zero_add]

theorem streamBytes_full (σ : State) (k : Nat) :
    streamBytes σ k 0 1008=Spec.MlDsa.G (B σ k) 1008 := by
  apply List.ext_getElem
  · rw [streamBytes_length,VG.Proof.MlDsa.Sample.G_length]
  · intro i hi hj
    simp only [streamBytes,List.getElem_map,List.getElem_range,Nat.zero_add,F]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
