import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- Physical destinations at the interface between the fused groups. -/
theorem renThree_data (outer : Bool) :
    (renThree outer).data = ⟨#[.v0,.v22,.v23,.v1,.v24,.v5,.v6,.v7], rfl⟩ := by
  cases outer <;> decide

theorem renThree_free (outer : Bool) : (renThree outer).free = .v21 := by
  cases outer <;> decide

theorem renThree_injective (outer : Bool) :
    Function.Injective (fun i : Fin 8 => (renThree outer).data[i.val]) := by
  rw [renThree_data]
  change ∀ i j : Fin 8, _ → i = j
  decide

theorem renThree_apart (outer : Bool) :
    ∀ i : Fin 8, (renThree outer).data[i.val] ≠ (renThree outer).free := by
  rw [renThree_data, renThree_free]
  decide

theorem table_length : staticNttWords.length = 488 := by
  simp only [staticNttWords, List.length_map, List.length_range, expandedVals,
    List.length_append, List.length_flatMap]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  decide

end VG.Proof.MlDsa.AArch64.Optimized
