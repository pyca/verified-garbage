import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassRead

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem allChecks_mem (i : Fin 2 × Fin 8) : i∈allChecks := pairIndices_mem i

theorem allChecks_nodup : allChecks.Nodup := by decide +kernel

theorem checkAddr_contains (base : Addr) {u : Nat} (hu : u<8) (i : Fin 2 × Fin 8) :
    (⟨base,2048⟩ : Region).Contains (checkAddr (base+BitVec.ofNat 64 (16*u)) i) 16 := by
  simp only [checkAddr,BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.contains_base base (by omega) (by omega)

/-- Every written vector has its exact final value, even when later slices
have run; inputs are read from the original memory and raw inverse bank. -/
theorem finalPass_read_written (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {n k : Nat} (hn : n≤8) (hk : k<n) (i : Fin 2 × Fin 8)
    (hw : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩) :
    (finalPassData hint work out aux c d n).mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16=
      checkOutput hint ((Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 i.1))[i.2.val])
        (d.mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16)
        (d.mem.read (checkAddr (aux+BitVec.ofNat 64 (16*k)) i) 16) c := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : k=n
    · subst k
      rw [finalPass_step hint work out aux c d (by omega) hw]
      rw [checkRun_read_slot _ _ _ _ _ _ _ i (allChecks_mem i) allChecks_nodup
        (fun j _ hne => checkAddr_sep _ hne)
        (fun j _ => ha.sep (checkAddr_contains aux (by omega) i) (checkAddr_contains out (by omega) j))]
      rw [finalPass_read_future hint work out aux c d (Nat.le_refl _) (by omega) i,
        finalPass_read_aux hint work out aux c d (by omega) (by omega) i ha]
    · rw [finalPassData,checkRun_read_other _ _ _ _ _ _ _ _
        (fun j _ => checkSlice_sep out (by omega) (by omega) he i j)]
      exact ih (by omega) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
