import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryInner

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def innerFieldPass (w : Poly) : Nat → Poly
  | 0 => w
  | u+1 => Traversal.run (Traversal.innerSlice u) (innerFieldPass w u)

theorem innerFieldPass_eq (w : Poly) (N : Nat) :
    innerFieldPass w N=Traversal.run ((List.range N).flatMap Traversal.innerSlice) w := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [innerFieldPass,ih,List.range_succ,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,Traversal.run_append]

theorem fivePassMem_step (m : Mem) (p : Addr) (u : Nat) :
    fivePassMem m p innerRoot tailRoot (u+1)=
      fiveMemStep (fivePassMem m p innerRoot tailRoot u) p u := by
  simp only [fivePassMem,fiveMemStep,coeffAddr,show 128*u=4*(32*u) by omega]

theorem fivePassMem_field_prefix {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-15*8380417) (15*8380417)) {N : Nat} (hn : N≤8) :
    SignedPolyIs (fivePassMem m p innerRoot tailRoot N) p (innerFieldPass w N)
      (-15*8380417) (15*8380417) ∧
    (∀ k<32*N, (coeffAt (fivePassMem m p innerRoot tailRoot N) p k).toNat<3*8380417) := by
  induction N with
  | zero => exact ⟨h,fun k hk => by omega⟩
  | succ N ih =>
    have hi := ih (by omega)
    have hs := fiveMemStep_field (u := N) (by omega) hi.1
    rw [fivePassMem_step]
    refine ⟨hs.1,?_⟩
    intro k hk
    by_cases he : k/32=N
    · exact hs.2 k (by omega) he
    · rw [fiveMemStep_outside _ _ (by omega) (by omega) he]
      exact hi.2 k (by omega)

/-- All eight slices finish in the positive internal representation, with the
same field polynomial as the exact inner NTT traversal. -/
theorem fivePassMem_field {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-15*8380417) (15*8380417)) :
    PosPolyIs (fivePassMem m p innerRoot tailRoot 8) p
      (Traversal.run Traversal.innerSchedule w) := by
  have hp := fivePassMem_field_prefix h (N := 8) (by decide)
  rw [innerFieldPass_eq] at hp
  constructor
  · intro k hk
    exact hp.2 k hk
  · apply ext_getElem!
    intro k hk
    rw [polyAt_get _ _ hk]
    have hb := hp.2 k hk
    have hv := hp.1.value k hk
    have ht := BitVec.toInt_eq_toNat_cond
      (coeffAt (fivePassMem m p innerRoot tailRoot 8) p k)
    have he : (coeffAt (fivePassMem m p innerRoot tailRoot 8) p k).toInt=
        ((coeffAt (fivePassMem m p innerRoot tailRoot 8) p k).toNat : Int) := by
      split at ht <;> omega
    rw [he] at hv
    have hc (j : Nat) : ofInt (j : Int)=ofNat j := by
      apply Fin.ext
      simp only [ofInt,ofNat,Fin.val_ofNat,← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]
    rw [hc] at hv
    exact hv

end VG.Proof.MlDsa.AArch64.Optimized
