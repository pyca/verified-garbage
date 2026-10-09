import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCanonicalBatch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseScale

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def halfPairs (half : Fin 2) : List (VReg × VReg) :=
  (List.finRange 4).map fun j => ((regs 7)[4*half.val+j.val],VG.Impl.MlDsa.AArch64.Optimized.Inverse.qt j.val)

def halfValues (half : Fin 2) (v : Vector (BitVec 128) 8) (q : BitVec 128) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => if 4*half.val≤j.val ∧ j.val<4*half.val+4 then canonicalVector v[j.val] q else v[j.val]

theorem half_geometry (half : Fin 2) :
    ((halfPairs half).map Prod.fst).Nodup ∧ ((halfPairs half).map Prod.snd).Nodup ∧
    (∀ p∈halfPairs half, p.1∉(halfPairs half).map Prod.snd) ∧
    (∀ p∈halfPairs half, p.2∉(halfPairs half).map Prod.fst) ∧
    .v31∉(halfPairs half).map Prod.fst ∧ .v31∉(halfPairs half).map Prod.snd := by
  revert half
  decide +kernel

theorem half_index (half : Fin 2) (j : Fin 8) :
    ((4*half.val≤j.val ∧ j.val<4*half.val+4) →
      ((regs 7)[j.val],VG.Impl.MlDsa.AArch64.Optimized.Inverse.qt (j.val-4*half.val))∈halfPairs half) ∧
    (¬(4*half.val≤j.val ∧ j.val<4*half.val+4) →
      (regs 7)[j.val]∉(halfPairs half).map Prod.snd++(halfPairs half).map Prod.fst) := by
  revert half j
  decide +kernel

theorem canonicalBank_ok (half : Fin 2)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Vector (BitVec 128) 8}
    (hb : Bank s (regs 7) v)
    (k : ∀ t, VChg runRegs s t → Bank t (regs 7) (halfValues half v (s.v .v31)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (canonicalBatchCode (halfPairs half) .v31 ++ rest)) s Q := by
  obtain ⟨hd,ht,hdt,htd,hqd,hqt⟩ := half_geometry half
  refine canonicalBatch_ok (halfPairs half) .v31 hd ht hdt htd hqd hqt fun t hc hv => ?_
  have hm : ∀ half : Fin 2, (halfPairs half).map Prod.snd++(halfPairs half).map Prod.fst⊆runRegs := by decide +kernel
  refine k t (hc.mono (hm half)) ?_
  intro j
  simp only [halfValues,Vector.getElem_ofFn]
  by_cases hj : 4*half.val≤j.val ∧ j.val<4*half.val+4
  · rw [ite_eq_left hj,hv _ ((half_index half j).1 hj),hb j]
  · rw [ite_eq_right hj,hc.get _ ((half_index half j).2 hj)]
    exact hb j

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
