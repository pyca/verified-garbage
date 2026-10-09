import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreV

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_ldrx)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (saved)

private theorem saved_inj : ∀ i<10, ∀ j<10, saved[i]! = saved[j]! ↔ i=j := by decide
private theorem saved_ne19 : ∀ i<9, saved[i+1]! ≠ Reg.x19 := by decide

/-- Restore x20 through x28 before restoring the scratch base in x19. -/
theorem restoreG_ok (s : State)
    (hr : ∀ i<9, InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (7976+8*i)) 8) :
    WP isa (.block ((List.range 9).map fun i => .ldr .x (saved[i+1]!) .x19 (7976+8*i))) s
      fun t => Only (saved.drop 1) s t ∧
        ∀ i<9, t.gpr (saved[i+1]!)=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (7976+8*i)) 64 := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k t => Only (saved.drop 1) s t ∧
      ∀ i<k, t.gpr (saved[i+1]!)=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (7976+8*i)) 64)
    (fun k t hk ⟨ht,hvals⟩ => ?_) 9 (Nat.le_refl _) s
    ⟨Only.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  have h19 : t.gpr .x19=s.gpr .x19 := ht.get .x19 (by decide)
  refine wp_ldrx ⟨by omega,by omega⟩ (by rw [h19])
    (by rw [ht.rd,ht.wr]; exact hr k hk) fun u hu eu => WP.block_nil_iff.mpr ⟨?_,fun i hi => ?_⟩
  · exact (ht.trans hu).mono (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · rw [List.mem_singleton.mp hr]
        have hm : ∀ j<9, saved[j+1]! ∈ saved.drop 1 := by decide
        exact hm k hk)
  · by_cases heq : i=k
    · subst i; rw [eu,ht.mem]
    · rw [hu.get (saved[i+1]!) (by
        simp only [List.mem_singleton,saved_inj (i+1) (by omega) (k+1) (by omega)]
        omega)]
      exact hvals i (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
