import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRestoreV
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.RestoreG

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_ldrx)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (restoreG oSave saved)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (saved_inj)

/-- Restore x20 through x28 while keeping the scratch base in x19. -/
theorem restoreG_with {v : Nat} {σ s : State} (he : Env v σ s)
    (hr : ∀d n,d+n≤8192 → InRegions (s.rd++s.wr) (at' σ d) n) :
    WP isa (.block restoreG) s fun t => Only (saved.drop 1) s t ∧
      ∀ i < 9,t.gpr (saved[i+1]!) = σ.gpr (saved[i+1]!) := by
  unfold restoreG
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k t => Only (saved.drop 1) s t ∧ ∀ i < k,t.gpr (saved[i+1]!) = σ.gpr (saved[i+1]!))
    (fun k t hk ⟨ht,hvals⟩ => ?_) 9 (Nat.le_refl _) s
    ⟨Only.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  have hin : InRegions (t.rd++t.wr) (at' σ (oSave+8*(k+1))) 8 := by
    rw [ht.rd,ht.wr]
    exact hr _ _ (by dsimp only [oSave]; omega)
  refine wp_ldrx ⟨by dsimp only [oSave]; omega,by dsimp only [oSave]; omega⟩
    (by rw [ht.get .x19,he.x19]; rfl) hin fun u hu eu => WP.block_nil_iff.mpr ⟨?_,fun i hi => ?_⟩
  · exact (ht.trans hu).mono (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · rw [List.mem_singleton.mp hr]
        exact (by
          have hm : ∀ j < 9,saved[j+1]! ∈ saved.drop 1 := by decide
          exact hm k hk))
  · by_cases heq : i = k
    · subst i
      rw [eu,ht.mem]
      exact he.savedG (k+1) (by omega)
    · rw [hu.get (saved[i+1]!) (by
        simp only [List.mem_singleton,saved_inj (i+1) (by omega) (k+1) (by omega)]
        omega)]
      exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
