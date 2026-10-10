import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSlot

/-! ## From `PairedPassRead.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- Different strided iterations touch disjoint output vectors. -/
theorem checkSlice_sep (out : Addr) {u k : Nat} (hu : u<8) (hk : k<8) (hne : k≠u)
    (i j : Fin 2 × Fin 8) :
    Mem.Sep (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16
      (checkAddr (out+BitVec.ofNat 64 (16*u)) j) 16 := by
  simp only [checkAddr,BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.sep out (by omega) (by omega) (by omega)

/-- A final-pass prefix has not overwritten vectors belonging to later slices. -/
theorem finalPass_read_future (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {u k : Nat} (hu : u≤k) (hk : k<8) (i : Fin 2 × Fin 8) :
    (finalPassData hint work out aux c d u).mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16=
      d.mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16 := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [finalPassData,checkRun_read_other _ _ _ _ _ _ _ _
      (fun j _ => checkSlice_sep out (by omega) hk (by omega) i j),ih (by omega)]

/-- Auxiliary input reads survive all final-pass output writes. -/
theorem finalPass_read_aux (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {u k : Nat} (hu : u≤8) (hk : k<8) (i : Fin 2 × Fin 8)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩) :
    (finalPassData hint work out aux c d u).mem.read (checkAddr (aux+BitVec.ofNat 64 (16*k)) i) 16=
      d.mem.read (checkAddr (aux+BitVec.ofNat 64 (16*k)) i) 16 := by
  apply (finalPass_frame hint work out aux c d hu).read (r:=⟨aux,2048⟩)
  · simp only [checkAddr,BitVec.add_assoc,←BitVec.ofNat_add]
    exact Offset.contains_base aux (by omega) (by omega)
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hd
  · decide

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedPassOutput.lean` -/

section

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

end
